/-
  Audit surfaces in Lean's own library (Section 5).

  For a sample of the theorems in `Init` and `Std`, this file measures three sets of
  constants:

  * the signature surface: the statement, the axioms the proof uses, and the types of all
    constants they mention, without the body of any definition;
  * the audit surface: the same, with the body of every definition that is reached;
  * the dependency closure: everything the kernel checked, proofs included.

  Sizes are numbers of constants and numbers of distinct source lines of code. A line of code
  has a character that is not white space and lies outside comments, so documentation does
  not count.

  Run it with `make measure`. It prints a report and writes the numbers and the tables that
  the paper includes into the directory `out`. The numbers depend on the Lean version in
  `lean-toolchain`.
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
constructors and its mutual block, and a constructor or a recursor always brings its
inductive type. -/
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

/-- For each line of a Lean source file, whether it is a line of code. Block comments nest. -/
def codeLines (text : String) : Array Bool := Id.run do
  let chars := text.toList.toArray
  let mut flags : Array Bool := #[]
  let mut depth := 0
  let mut inString := false
  let mut lineComment := false
  let mut hasCode := false
  let mut i := 0
  while i < chars.size do
    let c := chars[i]!
    let d := if i + 1 < chars.size then chars[i + 1]! else ' '
    if c == '\n' then
      flags := flags.push hasCode
      hasCode := false
      lineComment := false
      i := i + 1
    else if lineComment then
      i := i + 1
    else if depth > 0 then
      if c == '/' && d == '-' then
        depth := depth + 1
        i := i + 2
      else if c == '-' && d == '/' then
        depth := depth - 1
        i := i + 2
      else
        i := i + 1
    else if inString then
      hasCode := true
      if c == '\\' then
        i := i + 2
      else
        if c == '"' then inString := false
        i := i + 1
    else if c == '/' && d == '-' then
      depth := 1
      i := i + 2
    else if c == '-' && d == '-' then
      lineComment := true
      i := i + 2
    else if c == '\'' && d == '"' && i + 2 < chars.size && chars[i + 2]! == '\'' then
      hasCode := true
      i := i + 3
    else
      if c == '"' then inString := true
      if !c.isWhitespace then hasCode := true
      i := i + 1
  return flags.push hasCode

structure Cache where
  deps : Std.HashMap (Nat × Name) (Array Name) := {}
  /-- module index, first line, number of lines -/
  range : Std.HashMap Name (Option (Nat × Nat × Nat)) := {}
  /-- per module, the lines of code of its source file -/
  code : Std.HashMap Nat (Array Bool) := {}

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

/-- The lines of code of the source file of a module. -/
def codeOf (moduleIdx : Nat) : M (Array Bool) := do
  if let some flags := (← get).code[moduleIdx]? then return flags
  let name := (← getEnv).header.moduleNames[moduleIdx]!
  let path ← findLean (← getSrcSearchPath) name
  let flags := codeLines (← IO.FS.readFile path)
  modify fun c => { c with code := c.code.insert moduleIdx flags }
  return flags

/-- The distinct source lines covered by the declarations that introduce the constants of a
set: the lines of code, and all lines. Ranges may nest, as for a constructor inside its
inductive type. -/
def sourceLines (s : Std.HashSet Name) : M (Nat × Nat) := do
  let mut ranges : Std.HashSet (Nat × Nat × Nat) := {}
  for n in s do
    if let some r := ← rangeOf n then ranges := ranges.insert r
  let mut lines : Std.HashSet (Nat × Nat) := {}
  let mut code := 0
  for (m, first, len) in ranges do
    let flags ← codeOf m
    for i in [0:len] do
      let line := first + i
      unless lines.contains (m, line) do
        lines := lines.insert (m, line)
        if flags.getD (line - 1) false then code := code + 1
  return (code, lines.size)

structure Row where
  name : Name
  /-- `Init` or `Std` -/
  root : Name
  sig : Std.HashSet Name
  audit : Std.HashSet Name
  dep : Std.HashSet Name
  sigConsts : Nat
  sigLines : Nat
  auditConsts : Nat
  auditLines : Nat
  depConsts : Nat
  depLines : Nat
  /-- the lines of code of the theorem's own declaration, statement and proof -/
  ownLines : Nat
  axiomNames : Array Name

def measure (thm : Name) : M Row := do
  let env ← getEnv
  let some ci := env.find? thm | throwError "unknown constant {thm}"
  let root := match env.getModuleIdxFor? thm with
    | some idx => env.header.moduleNames[idx.toNat]!.getRoot
    | none => .anonymous
  let dep ← closure .full #[thm]
  let axioms := dep.toArray.filter fun n =>
    match env.find? n with
    | some (.axiomInfo _) => true
    | _ => false
  let seeds := exprNames ci.type ++ axioms
  let sig ← closure .sig seeds
  let audit ← closure .stmt seeds
  return {
    name := thm, root, sig, audit, dep
    sigConsts := sig.size
    sigLines := (← sourceLines sig).1
    auditConsts := audit.size
    auditLines := (← sourceLines audit).1
    depConsts := dep.size
    depLines := (← sourceLines dep).1
    ownLines := (← sourceLines (({} : Std.HashSet Name).insert thm)).1
    axiomNames := axioms }

/-! ## Statistics and output -/

/-- The `p`-th percentile of an array. -/
def pct (xs : Array Nat) (p : Nat) : Nat :=
  let s := xs.qsort (· < ·)
  if s.isEmpty then 0 else s[(p * (s.size - 1)) / 100]!

def median (xs : Array Nat) : Nat := pct xs 50

/-- The mean, rounded to the nearest integer. -/
def mean (xs : Array Nat) : Nat :=
  if xs.isEmpty then 0 else (2 * xs.foldl (· + ·) 0 + xs.size) / (2 * xs.size)

/-- `a / b` in tenths, rounded to the nearest tenth. -/
def tenths (a b : Nat) : Nat :=
  if b == 0 then 0 else (20 * a + b) / (2 * b)

/-- A number with separators between thousands. -/
def commas (n : Nat) : String :=
  let digits := (toString n).toList.reverse
  let rec go : List Char → Nat → List Char
    | [], _ => []
    | c :: rest, i =>
      if i > 0 && i % 3 == 0 then ',' :: c :: go rest (i + 1) else c :: go rest (i + 1)
  String.ofList (go digits 0).reverse

/-- A number of tenths as a decimal. -/
def decimal (t : Nat) : String := s!"{t / 10}.{t % 10}"

def summary (label : String) (xs : Array Nat) : String :=
  s!"{label}: min {pct xs 0}, p25 {pct xs 25}, median {pct xs 50}, p75 {pct xs 75}, " ++
    s!"p90 {pct xs 90}, max {pct xs 100}, mean {mean xs}"

def tableRow (label : String) (xs : Array Nat) : String :=
  s!"{label} & {commas (pct xs 25)} & {commas (pct xs 50)} & {commas (pct xs 75)} & " ++
    s!"{commas (pct xs 90)} & {commas (pct xs 100)} & {commas (mean xs)} \\\\"

/-- A theorem counts as written by hand when its module is in `Init` or `Std`, its name is
not internal, and it has a source range of its own. -/
def isSampled (env : Environment) (n : Name) (ci : ConstantInfo) : MetaM Bool := do
  let .thmInfo _ := ci | return false
  if n.isInternalDetail then return false
  let some idx := env.getModuleIdxFor? n | return false
  let root := env.header.moduleNames[idx.toNat]!.getRoot
  unless root == `Init || root == `Std do return false
  return (← findDeclarationRangesCore? n).isSome

def texName (n : Name) : String :=
  "\\lean{" ++ (toString n).replace "_" "\\_" ++ "}"

def texMacro (name value : String) : String :=
  "\\newcommand{\\" ++ name ++ "}{" ++ value ++ "}\n"

def run (sampleSize : Nat) (examples tableExamples : Array Name) : MetaM Unit := do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ← isSampled env n ci then names := names.push n
  let sorted := names.qsort (fun a b => a.toString < b.toString)
  -- evenly spaced over the whole order of names
  let sample := (Array.range sampleSize).map fun i => sorted[i * sorted.size / sampleSize]!
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
  let sigC := rows.map (·.sigConsts)
  let audC := rows.map (·.auditConsts)
  let depC := rows.map (·.depConsts)
  let sigL := rows.map (·.sigLines)
  let audL := rows.map (·.auditLines)
  let depL := rows.map (·.depLines)
  let ownL := rows.map (·.ownLines)
  let ratioC := median (rows.map fun r => tenths r.depConsts r.auditConsts)
  let ratioL := median (rows.map fun r => tenths r.depLines r.auditLines)
  let ratioSig := median (rows.map fun r => tenths r.auditLines r.sigLines)
  let half := (rows.filter fun r => r.auditLines * 2 ≤ r.depLines).size
  let atMost (k : Nat) := (rows.filter fun r => r.auditLines ≤ k).size
  let initRows := rows.filter (·.root == `Init)
  let stdRows := rows.filter (·.root == `Std)
  let allAxioms := rows.foldl (init := ({} : Std.HashSet Name)) fun acc r =>
    r.axiomNames.foldl (init := acc) fun acc a => acc.insert a
  let axiomList := (allAxioms.toArray.map (·.toString)).qsort (· < ·)
  let noAxioms := (rows.filter fun r => r.axiomNames.isEmpty).size
  let (uSigC, uSigL) := unions[0]!
  let (uAudC, uAudL) := unions[1]!
  let (uDepC, uDepL) := unions[2]!
  -- the report
  IO.println s!"Lean {Lean.versionString}"
  IO.println s!"theorems written by hand in Init and Std: {sorted.size}"
  IO.println s!"sample: {sample.size} theorems, evenly spaced in the order of names"
  IO.println s!"  of these in Init: {initRows.size}, in Std: {stdRows.size}"
  IO.println (summary "signature surface, constants" sigC)
  IO.println (summary "audit surface, constants" audC)
  IO.println (summary "dependency closure, constants" depC)
  IO.println (summary "signature surface, lines of code" sigL)
  IO.println (summary "audit surface, lines of code" audL)
  IO.println (summary "dependency closure, lines of code" depL)
  IO.println (summary "the theorem's own declaration, lines of code" ownL)
  IO.println (summary "Init only: audit surface, lines of code" (initRows.map (·.auditLines)))
  IO.println (summary "Init only: dependency closure, lines of code" (initRows.map (·.depLines)))
  IO.println (summary "Std only: audit surface, lines of code" (stdRows.map (·.auditLines)))
  IO.println (summary "Std only: dependency closure, lines of code" (stdRows.map (·.depLines)))
  IO.println s!"median of closure/audit, constants: {decimal ratioC}"
  IO.println s!"median of closure/audit, lines of code: {decimal ratioL}"
  IO.println s!"median of audit/signature, lines of code: {decimal ratioSig}"
  IO.println s!"theorems whose audit surface is at most half of the closure, in lines: {half}"
  IO.println (s!"theorems whose audit surface is at most 100, 200, 500 lines of code: " ++
    s!"{atMost 100}, {atMost 200}, {atMost 500}")
  IO.println s!"axioms that occur: {axiomList.toList}"
  IO.println s!"theorems that use no axiom: {noAxioms}"
  IO.println ("union over the sample, constants, lines of code, all lines: " ++
    s!"signature {uSigC} {uSigL.1} {uSigL.2}, audit {uAudC} {uAudL.1} {uAudL.2}, " ++
    s!"closure {uDepC} {uDepL.1} {uDepL.2}")
  IO.println ("examples: name, signature constants and lines, audit constants and lines, " ++
    "closure constants and lines, axioms")
  for r in exRows do
    IO.println (s!"  {r.name}, {r.sigConsts}, {r.sigLines}, {r.auditConsts}, {r.auditLines}, " ++
      s!"{r.depConsts}, {r.depLines}, {r.axiomNames.size}")
  -- the files that the paper includes
  let numbers := String.join [
    "% Written by Measure.lean. Do not edit.\n",
    texMacro "LeanVersion" Lean.versionString,
    texMacro "NumPopulation" (commas sorted.size),
    texMacro "NumSample" (commas sample.size),
    texMacro "NumInit" (commas initRows.size),
    texMacro "NumStd" (commas stdRows.size),
    texMacro "SigLinesMedian" (commas (median sigL)),
    texMacro "AuditLinesMedian" (commas (median audL)),
    texMacro "ClosureLinesMedian" (commas (median depL)),
    texMacro "OwnLinesMedian" (commas (median ownL)),
    texMacro "InitAuditLinesMedian" (commas (median (initRows.map (·.auditLines)))),
    texMacro "InitClosureLinesMedian" (commas (median (initRows.map (·.depLines)))),
    texMacro "StdAuditLinesMedian" (commas (median (stdRows.map (·.auditLines)))),
    texMacro "StdClosureLinesMedian" (commas (median (stdRows.map (·.depLines)))),
    texMacro "RatioClosureAuditConsts" (decimal ratioC),
    texMacro "RatioClosureAuditLines" (decimal ratioL),
    texMacro "RatioAuditSigLines" (decimal ratioSig),
    texMacro "NumAuditHalf" (commas half),
    texMacro "NumAuditAtMostHundred" (commas (atMost 100)),
    texMacro "NumAuditAtMostFiveHundred" (commas (atMost 500)),
    texMacro "NumNoAxiom" (commas noAxioms),
    texMacro "AxiomsUsed" (String.intercalate ", " (axiomList.toList.map fun a =>
      "\\lean{" ++ a.replace "_" "\\_" ++ "}")),
    texMacro "UnionAuditConsts" (commas uAudC),
    texMacro "UnionAuditLines" (commas uAudL.1),
    texMacro "UnionClosureConsts" (commas uDepC),
    texMacro "UnionClosureLines" (commas uDepL.1),
    texMacro "UnionAuditPercent" (toString ((200 * uAudL.1 + uDepL.1) / (2 * uDepL.1))),
    texMacro "CommentPercent" (toString ((200 * (uAudL.2 - uAudL.1) + uAudL.2) / (2 * uAudL.2)))]
  let sizes := String.intercalate "\n" [
    tableRow "Constants & signature surface" sigC,
    tableRow " & audit surface" audC,
    tableRow " & dependency closure" depC,
    "\\midrule",
    tableRow "Lines of code & signature surface" sigL,
    tableRow " & audit surface" audL,
    tableRow " & dependency closure" depL] ++ "\n"
  let exampleRows := exRows.filter fun r => tableExamples.contains r.name
  let exampleTable := String.intercalate "\n" (exampleRows.toList.map fun r =>
    s!"{texName r.name} & {commas r.sigConsts} & {commas r.sigLines} & {commas r.auditConsts} & " ++
      s!"{commas r.auditLines} & {commas r.depConsts} & {commas r.depLines} \\\\") ++ "\n"
  IO.FS.createDirAll "out"
  IO.FS.writeFile "out/numbers.tex" numbers
  IO.FS.writeFile "out/table-sizes.tex" ("% Written by Measure.lean. Do not edit.\n" ++ sizes)
  IO.FS.writeFile "out/table-examples.tex"
    ("% Written by Measure.lean. Do not edit.\n" ++ exampleTable)

end AuditMeasure

#eval AuditMeasure.run 2000
  #[``Nat.add_comm, ``Nat.mul_comm, ``Nat.gcd_comm, ``List.length_append, ``List.reverse_reverse,
    ``List.map_map, ``Array.size_push, ``Option.map_map, ``String.length_append,
    ``Std.HashMap.size_insert, ``Std.HashMap.getElem?_insert, ``Std.TreeMap.contains_insert]
  #[``Nat.add_comm, ``List.reverse_reverse, ``Array.size_push, ``Nat.gcd_comm,
    ``String.length_append, ``Std.HashMap.size_insert, ``Std.TreeMap.contains_insert]
