/-
  Audit surfaces in Lean's own library (Section 5).

  For a sample of the theorems in `Init` and `Std`, this file measures three sets of
  constants, in constants and in source lines:

  * the signature surface: the statement, the axioms the proof uses, and the types of all
    constants they mention, without the body of any definition;
  * the audit surface: the same, with the body of every definition that is reached;
  * the dependency closure: everything the kernel checked, proofs included.

  Sizes are numbers of constants and numbers of distinct source lines.

  Run it with `make measure`. The numbers depend on the Lean version in `lean-toolchain`.
-/
import Lean
import Std
open Lean

namespace AuditMeasure

/-- The names an expression refers to: its constants, the structure of each projection, and
the type of each literal. -/
def exprNames (e : Expr) : Array Name :=
  let s : Std.HashSet Name := runST fun σ => do
    let act : StateRefT' σ (Std.HashSet Name) (ST σ) Unit := e.forEach' fun sub => do
      match sub with
      | .const n _ => modify (·.insert n); pure false
      | .proj s _ _ => modify (·.insert s); pure true
      | .lit (.natVal _) => modify (·.insert ``Nat); pure false
      | .lit (.strVal _) => modify (·.insert ``String); pure false
      | _ => pure true
    let (_, s) ← act.run {}
    pure s
  s.toArray

/-- How much of a constant is followed. -/
inductive Mode where
  /-- types only -/
  | sig
  /-- types and the bodies of definitions -/
  | stmt
  /-- types, the bodies of definitions and opaque constants, and the proofs of theorems -/
  | full
  deriving BEq

def Mode.idx : Mode → Nat
  | .sig => 0
  | .stmt => 1
  | .full => 2

/-- The direct dependencies of a constant in a mode. An inductive type always brings its
constructors, and a constructor or a recursor always brings its inductive type. -/
def directDeps (ci : ConstantInfo) (mode : Mode) : Array Name :=
  let ty := exprNames ci.type
  match ci with
  | .defnInfo v => if mode == .sig then ty else ty ++ exprNames v.value
  | .thmInfo v => if mode == .full then ty ++ exprNames v.value else ty
  | .opaqueInfo v => if mode == .full then ty ++ exprNames v.value else ty
  | .inductInfo v => ty ++ v.ctors.toArray ++ v.all.toArray
  | .ctorInfo v => ty.push v.induct
  | .recInfo v => ty ++ v.all.toArray
  | .axiomInfo _ => ty
  | .quotInfo _ => ty

structure Cache where
  deps : Std.HashMap (Nat × Name) (Array Name) := {}
  /-- module index, first line, number of lines -/
  range : Std.HashMap Name (Option (Nat × Nat × Nat)) := {}

abbrev M := StateT Cache MetaM

def deps (mode : Mode) (n : Name) : M (Array Name) := do
  if let some ds := (← get).deps[(mode.idx, n)]? then return ds
  let ds := match (← getEnv).find? n with
    | some ci => directDeps ci mode
    | none => #[]
  modify fun c => { c with deps := c.deps.insert (mode.idx, n) ds }
  return ds

/-- All constants reachable from the seeds. -/
def closure (mode : Mode) (seeds : Array Name) : M (Std.HashSet Name) := do
  let mut seen : Std.HashSet Name := {}
  let mut todo : List Name := seeds.toList
  repeat
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      unless seen.contains n do
        seen := seen.insert n
        for d in (← deps mode n) do
          unless seen.contains d do
            todo := d :: todo
  return seen

/-- The source range of the declaration that introduces a constant. -/
def rangeOf (n : Name) : M (Option (Nat × Nat × Nat)) := do
  if let some r := (← get).range[n]? then return r
  let env ← getEnv
  let r ← match (← findDeclarationRanges? n), env.getModuleIdxFor? n with
    | some rs, some idx =>
      pure (some (idx.toNat, rs.range.pos.line, rs.range.endPos.line - rs.range.pos.line + 1))
    | _, _ => pure none
  modify fun c => { c with range := c.range.insert n r }
  return r

/-- The number of distinct source lines covered by the declarations that introduce the
constants of a set. Ranges may nest, as for a constructor inside its inductive type. -/
def sourceLines (s : Std.HashSet Name) : M Nat := do
  let mut ranges : Std.HashSet (Nat × Nat × Nat) := {}
  for n in s do
    if let some r := ← rangeOf n then ranges := ranges.insert r
  let mut lines : Std.HashSet (Nat × Nat) := {}
  for (m, first, len) in ranges do
    for i in [0:len] do
      lines := lines.insert (m, first + i)
  return lines.size

structure Row where
  name : Name
  sig : Std.HashSet Name
  audit : Std.HashSet Name
  dep : Std.HashSet Name
  sigConsts : Nat
  sigLines : Nat
  auditConsts : Nat
  auditLines : Nat
  depConsts : Nat
  depLines : Nat
  axioms : Nat
  axiomNames : Array Name

def measure (thm : Name) : M Row := do
  let env ← getEnv
  let some ci := env.find? thm | throwError "unknown constant {thm}"
  let dep ← closure .full #[thm]
  let axioms := dep.toArray.filter fun n =>
    match env.find? n with
    | some (.axiomInfo _) => true
    | _ => false
  let seeds := exprNames ci.type ++ axioms
  let sig ← closure .sig seeds
  let audit ← closure .stmt seeds
  return {
    name := thm
    sig, audit, dep
    sigConsts := sig.size
    sigLines := ← sourceLines sig
    auditConsts := audit.size
    auditLines := ← sourceLines audit
    depConsts := dep.size
    depLines := ← sourceLines dep
    axioms := axioms.size
    axiomNames := axioms }

/-- The `p`-th percentile of a sorted array. -/
def pct (xs : Array Nat) (p : Nat) : Nat :=
  if xs.isEmpty then 0 else xs[(p * (xs.size - 1)) / 100]!

def summary (label : String) (xs : Array Nat) : String :=
  let s := xs.qsort (· < ·)
  let mean := if s.isEmpty then 0 else (s.foldl (· + ·) 0) / s.size
  s!"{label}: min {pct s 0}, p25 {pct s 25}, median {pct s 50}, p75 {pct s 75}, " ++
    s!"p90 {pct s 90}, max {pct s 100}, mean {mean}"

/-- A theorem counts as written by hand when its module is in `Init` or `Std`, its name is
not internal, and it has a source range of its own. -/
def isSampled (env : Environment) (n : Name) (ci : ConstantInfo) : MetaM Bool := do
  let .thmInfo _ := ci | return false
  if n.isInternalDetail then return false
  let some idx := env.getModuleIdxFor? n | return false
  let root := env.header.moduleNames[idx.toNat]!.getRoot
  unless root == `Init || root == `Std do return false
  return (← findDeclarationRangesCore? n).isSome

def run (sampleSize : Nat) (examples : Array Name) : MetaM Unit := do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ← isSampled env n ci then names := names.push n
  let sorted := names.qsort (fun a b => a.toString < b.toString)
  let stride := max 1 (sorted.size / sampleSize)
  let mut sample : Array Name := #[]
  for i in [0:sorted.size] do
    if i % stride == 0 && sample.size < sampleSize then sample := sample.push sorted[i]!
  IO.println s!"Lean {Lean.versionString}"
  IO.println s!"theorems written by hand in Init and Std: {sorted.size}"
  IO.println s!"sample: every {stride}th in name order, {sample.size} theorems"
  let (rows, exRows, unions) ← (do
    let mut rows : Array Row := #[]
    let mut uSig : Std.HashSet Name := {}
    let mut uAudit : Std.HashSet Name := {}
    let mut uDep : Std.HashSet Name := {}
    for n in sample do
      let r ← measure n
      uSig := r.sig.fold (init := uSig) fun acc x => acc.insert x
      uAudit := r.audit.fold (init := uAudit) fun acc x => acc.insert x
      uDep := r.dep.fold (init := uDep) fun acc x => acc.insert x
      rows := rows.push { r with sig := {}, audit := {}, dep := {} }
    let unions := #[
      (uSig.size, ← sourceLines uSig), (uAudit.size, ← sourceLines uAudit),
      (uDep.size, ← sourceLines uDep)]
    let mut exRows : Array Row := #[]
    for n in examples do
      if (← getEnv).contains n then
        let r ← measure n
        exRows := exRows.push { r with sig := {}, audit := {}, dep := {} }
    return (rows, exRows, unions) : M _).run' {}
  IO.println (summary "signature surface, constants" (rows.map (·.sigConsts)))
  IO.println (summary "audit surface, constants" (rows.map (·.auditConsts)))
  IO.println (summary "dependency closure, constants" (rows.map (·.depConsts)))
  IO.println (summary "signature surface, source lines" (rows.map (·.sigLines)))
  IO.println (summary "audit surface, source lines" (rows.map (·.auditLines)))
  IO.println (summary "dependency closure, source lines" (rows.map (·.depLines)))
  IO.println (summary "axioms used" (rows.map (·.axioms)))
  let allAxioms := rows.foldl (init := ({} : Std.HashSet Name)) fun acc r =>
    r.axiomNames.foldl (init := acc) fun acc a => acc.insert a
  let axiomList := (allAxioms.toArray.map (·.toString)).qsort (· < ·)
  IO.println s!"axioms that occur: {axiomList.toList}"
  let noAxioms := (rows.filter fun r => r.axioms == 0).size
  IO.println s!"theorems that use no axiom: {noAxioms}"
  IO.println (summary "closure/audit ratio x10, constants"
    (rows.map fun r => r.depConsts * 10 / max 1 r.auditConsts))
  IO.println (summary "closure/audit ratio x10, source lines"
    (rows.map fun r => r.depLines * 10 / max 1 r.auditLines))
  IO.println (summary "audit/signature ratio x10, source lines"
    (rows.map fun r => r.auditLines * 10 / max 1 r.sigLines))
  let half := (rows.filter fun r => r.auditLines * 2 ≤ r.depLines).size
  IO.println s!"theorems whose audit surface is at most half of the closure, in lines: {half}"
  let small := (rows.filter fun r => r.auditLines ≤ 500).size
  IO.println s!"theorems whose audit surface is at most 500 lines: {small}"
  let smallSig := (rows.filter fun r => r.sigLines ≤ 500).size
  IO.println s!"theorems whose signature surface is at most 500 lines: {smallSig}"
  IO.println (s!"union over the sample, constants and lines: signature {unions[0]!.1} {unions[0]!.2}, " ++
    s!"audit {unions[1]!.1} {unions[1]!.2}, closure {unions[2]!.1} {unions[2]!.2}")
  IO.println ("examples: name, signature constants and lines, audit constants and lines, " ++
    "closure constants and lines, axioms")
  for r in exRows do
    IO.println (s!"  {r.name}, {r.sigConsts}, {r.sigLines}, {r.auditConsts}, {r.auditLines}, " ++
      s!"{r.depConsts}, {r.depLines}, {r.axioms}")

end AuditMeasure

#eval AuditMeasure.run 2000 #[
  ``Nat.add_comm, ``Nat.mul_comm, ``Nat.gcd_comm, ``List.length_append, ``List.reverse_reverse,
  ``List.map_map, ``Array.size_push, ``Option.map_map, ``String.length_append,
  ``Std.HashMap.size_insert, ``Std.HashMap.getElem?_insert, ``Std.TreeMap.contains_insert ]
