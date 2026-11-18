/-
  Reading laws instead of bodies: the interface surface and its soundness (Section 4).

  This file imports `Audit.lean` of this directory, which the Makefile compiles first. It
  appeared before as the artifact of the paper "Reading Laws Instead of Bodies" (tpp:2), which
  this paper supersedes.
-/
import Audit

namespace Audit

/-! ## Laws: theorems that stay (Section 4.1) -/

/-- An entry stays when it is a definition, an axiom, or a theorem in `T`. -/
def Entry.lawOrOther (T : Name → Bool) : Entry → Bool
  | Entry.defn _ _ => true
  | Entry.axm _ _ _ => true
  | Entry.thm h _ _ _ => T h

/-- The library without the theorems outside `T`. The theorems in `T` are the laws. -/
def keepLaws (T : Name → Bool) (L : Lib) : Lib := L.filter (Entry.lawOrOther T)

/-- Inline every theorem outside `T` into a proof, newest first. -/
def unfoldExcept (T : Name → Bool) : Lib → Pf → Pf
  | [], p => p
  | Entry.defn _ _ :: L, p => unfoldExcept T L p
  | Entry.axm _ _ _ :: L, p => unfoldExcept T L p
  | Entry.thm h _ _ q :: L, p =>
    if T h then unfoldExcept T L p else unfoldExcept T L (Pf.inlineLem h q p)

/-- Cut for the theorems outside `T`. The entries in `D` are newer and have other names. -/
theorem lemma_elim_except {T : Name → Bool} {L : Lib} (hwf : WF L) :
    ∀ (D : Lib) (p : Pf) (l r : Tm), (∀ e ∈ D, ∀ e' ∈ L, e.name ≠ e'.name) →
      Chk (D ++ L) p l r → Chk (D ++ keepLaws T L) (unfoldExcept T L p) l r := by
  induction hwf with
  | nil =>
    intro D p l r _ hc
    simpa [keepLaws, unfoldExcept] using hc
  | @defn L c u _ hfresh _ _ ih =>
    intro D p l r hD hc
    have hD' : ∀ e ∈ D ++ [Entry.defn c u], ∀ e' ∈ L, e.name ≠ e'.name := by
      intro e he e' he'
      rcases List.mem_append.mp he with h | h
      · exact hD e h e' (List.Mem.tail _ he')
      · have : e = Entry.defn c u := by simpa using h
        rw [this]
        exact fun eq => (hfresh e' he').1 eq.symm
    have := ih (D ++ [Entry.defn c u]) p l r hD' (by simpa using hc)
    have e1 : keepLaws T (Entry.defn c u :: L) = Entry.defn c u :: keepLaws T L := rfl
    have e2 : unfoldExcept T (Entry.defn c u :: L) p = unfoldExcept T L p := rfl
    rw [e1, e2]
    simpa using this
  | @axm L a l' r' _ hfresh ih =>
    intro D p l r hD hc
    have hD' : ∀ e ∈ D ++ [Entry.axm a l' r'], ∀ e' ∈ L, e.name ≠ e'.name := by
      intro e he e' he'
      rcases List.mem_append.mp he with h | h
      · exact hD e h e' (List.Mem.tail _ he')
      · have : e = Entry.axm a l' r' := by simpa using h
        rw [this]
        exact fun eq => (hfresh e' he').1 eq.symm
    have := ih (D ++ [Entry.axm a l' r']) p l r hD' (by simpa using hc)
    have e1 : keepLaws T (Entry.axm a l' r' :: L) = Entry.axm a l' r' :: keepLaws T L := rfl
    have e2 : unfoldExcept T (Entry.axm a l' r' :: L) p = unfoldExcept T L p := rfl
    rw [e1, e2]
    simpa using this
  | @thm L h l' r' q _ hfresh hq ih =>
    intro D p l r hD hc
    by_cases hT : T h = true
    · have hD' : ∀ e ∈ D ++ [Entry.thm h l' r' q], ∀ e' ∈ L, e.name ≠ e'.name := by
        intro e he e' he'
        rcases List.mem_append.mp he with h1 | h1
        · exact hD e h1 e' (List.Mem.tail _ he')
        · have : e = Entry.thm h l' r' q := by simpa using h1
          rw [this]
          exact fun eq => (hfresh e' he').1 eq.symm
      have := ih (D ++ [Entry.thm h l' r' q]) p l r hD' (by simpa using hc)
      simpa [keepLaws, unfoldExcept, Entry.lawOrOther, hT] using this
    · have hT' : T h = false := by simpa using hT
      have hc' : Chk (D ++ L) (Pf.inlineLem h q p) l r := by
        refine Chk.inlineLem (L := D ++ Entry.thm h l' r' q :: L) (l0 := l') (r0 := r')
          ?_ ?_ ?_ ?_ ?_ hc
        · intro l1 r1 q1 hm
          rcases mem_mid.mp hm with hm | hm
          · cases hm; exact ⟨rfl, rfl⟩
          · rcases List.mem_append.mp hm with hm | hm
            · exact absurd rfl
                (hD (Entry.thm h l1 r1 q1) hm (Entry.thm h l' r' q) (List.Mem.head _))
            · exact absurd rfl (hfresh _ hm).1
        · exact hq.weaken (fun e he => List.mem_append_right D he)
        · intro d u hm
          rcases mem_mid.mp hm with hm | hm
          · cases hm
          · exact hm
        · intro a l1 r1 hm
          rcases mem_mid.mp hm with hm | hm
          · cases hm
          · exact hm
        · intro h' l1 r1 q1 hm hne
          rcases mem_mid.mp hm with hm | hm
          · cases hm; exact absurd rfl hne
          · exact hm
      have := ih D _ l r (fun e he e' he' => hD e he e' (List.Mem.tail _ he')) hc'
      simpa [keepLaws, unfoldExcept, Entry.lawOrOther, hT'] using this

/-! ## Laws become axioms (Section 4.1) -/

/-- A theorem as an axiom with the same name and statement. -/
def Entry.asAxiom : Entry → Entry
  | Entry.defn c u => Entry.defn c u
  | Entry.axm a l r => Entry.axm a l r
  | Entry.thm h l r _ => Entry.axm h l r

def lawsAsAxioms (L : Lib) : Lib := L.map Entry.asAxiom

/-- A proof in which every use of a theorem is a use of the axiom of the same name. -/
def Pf.lemAsAx : Pf → Pf
  | .refl t => .refl t
  | .symm p => .symm (lemAsAx p)
  | .trans p q => .trans (lemAsAx p) (lemAsAx q)
  | .app p q => .app (lemAsAx p) (lemAsAx q)
  | .lam p => .lam (lemAsAx p)
  | .beta b a => .beta b a
  | .delta c => .delta c
  | .ax a => .ax a
  | .lem h => .ax h

theorem Entry.asAxiom_name (e : Entry) : e.asAxiom.name = e.name := by cases e <;> rfl

theorem Entry.asAxiom_consts (e : Entry) : e.asAxiom.consts = e.consts := by cases e <;> rfl

theorem Chk.lemAsAx {L : Lib} {p : Pf} {l r : Tm} (hc : Chk L p l r) :
    Chk (lawsAsAxioms L) (Pf.lemAsAx p) l r := by
  induction hc with
  | refl t => exact Chk.refl t
  | symm _ ih => exact Chk.symm ih
  | trans _ _ ih1 ih2 => exact Chk.trans ih1 ih2
  | app _ _ ih1 ih2 => exact Chk.app ih1 ih2
  | lam _ ih => exact Chk.lam ih
  | beta b a => exact Chk.beta b a
  | @delta c u hm => exact Chk.delta (List.mem_map.mpr ⟨Entry.defn c u, hm, rfl⟩)
  | @ax a l r hm => exact Chk.ax (List.mem_map.mpr ⟨Entry.axm a l r, hm, rfl⟩)
  | @lem h l r q hm => exact Chk.ax (List.mem_map.mpr ⟨Entry.thm h l r q, hm, rfl⟩)

theorem Pf.deltaRefs_lemAsAx (p : Pf) : (Pf.lemAsAx p).deltaRefs = p.deltaRefs := by
  induction p with
  | refl t => rfl
  | symm p ih => simpa [Pf.lemAsAx, Pf.deltaRefs] using ih
  | trans p q ihp ihq => simp [Pf.lemAsAx, Pf.deltaRefs, ihp, ihq]
  | app p q ihp ihq => simp [Pf.lemAsAx, Pf.deltaRefs, ihp, ihq]
  | lam p ih => simpa [Pf.lemAsAx, Pf.deltaRefs] using ih
  | beta b a => rfl
  | delta c => rfl
  | ax a => rfl
  | lem h => rfl

theorem lawsAsAxioms_noThm (L : Lib) : ∀ e ∈ lawsAsAxioms L, e.isThm = false := by
  intro e he
  obtain ⟨e0, _, rfl⟩ := List.mem_map.mp he
  cases e0 <;> rfl

/-- The laws as axioms, with the other theorems removed, form a well-formed library. -/
theorem WF.keepLawsAsAxioms {T : Name → Bool} {L : Lib} (hwf : WF L) :
    WF (lawsAsAxioms (keepLaws T L)) := by
  have fresh : ∀ {n : Name} {K : Lib}, Fresh n K → Fresh n (lawsAsAxioms (keepLaws T K)) := by
    intro n K hf e he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
    rw [Entry.asAxiom_name, Entry.asAxiom_consts]
    exact hf e0 (List.mem_filter.mp he0).1
  induction hwf with
  | nil => exact WF.nil
  | @defn L c u _ hf hcl hcu ih =>
    have e1 : lawsAsAxioms (keepLaws T (Entry.defn c u :: L))
        = Entry.defn c u :: lawsAsAxioms (keepLaws T L) := rfl
    rw [e1]
    exact WF.defn ih (fresh hf) hcl hcu
  | @axm L a l r _ hf ih =>
    have e1 : lawsAsAxioms (keepLaws T (Entry.axm a l r :: L))
        = Entry.axm a l r :: lawsAsAxioms (keepLaws T L) := rfl
    rw [e1]
    exact WF.axm ih (fresh hf)
  | @thm L h l r q _ hf _ ih =>
    by_cases hT : T h = true
    · have e1 : lawsAsAxioms (keepLaws T (Entry.thm h l r q :: L))
          = Entry.axm h l r :: lawsAsAxioms (keepLaws T L) := by
        simp [lawsAsAxioms, keepLaws, Entry.lawOrOther, Entry.asAxiom, hT]
      rw [e1]
      exact WF.axm ih (fresh hf)
    · have e1 : lawsAsAxioms (keepLaws T (Entry.thm h l r q :: L))
          = lawsAsAxioms (keepLaws T L) := by
        simp [lawsAsAxioms, keepLaws, Entry.lawOrOther, hT]
      rw [e1]
      exact ih

/-! ## Subjects: definitions that are not read (Section 4.1) -/

/-- An entry stays when it is an axiom or a definition outside `C`. The definitions in `C` are
the subjects. The function is used on libraries without theorems. -/
def Entry.notSubject (C : Name → Bool) : Entry → Bool
  | Entry.defn c _ => !C c
  | Entry.axm _ _ _ => true
  | Entry.thm _ _ _ _ => false

def dropSubjects (C : Name → Bool) (L : Lib) : Lib := L.filter (Entry.notSubject C)

/-- A proof that unfolds no subject checks without the definitions of the subjects. -/
theorem Chk.dropSubjects {C : Name → Bool} {L : Lib} {p : Pf} {l r : Tm} (hc : Chk L p l r)
    (hthm : ∀ e ∈ L, e.isThm = false) (hseal : ∀ c ∈ p.deltaRefs, C c = false) :
    Chk (dropSubjects C L) p l r := by
  refine hc.mono_refs ?_ ?_ ?_
  · intro d u hd hm
    exact List.mem_filter.mpr ⟨hm, by simp [Entry.notSubject, hseal d hd]⟩
  · intro a l r _ hm
    exact List.mem_filter.mpr ⟨hm, rfl⟩
  · intro h l r q _ hm
    have := hthm _ hm
    simp [Entry.isThm] at this

/-! ## The interface surface (Section 4.1) -/

/-- The library as a reader of the interface sees it: the laws are axioms, the other theorems
are gone, and the subjects have no definition. -/
def ifaceBase (T C : Name → Bool) (L : Lib) : Lib :=
  dropSubjects C (lawsAsAxioms (keepLaws T L))

/-- The proof in which the theorems outside `T` are inlined and the laws are used as axioms. -/
def ifaceProof (T : Name → Bool) (L : Lib) (p : Pf) : Pf :=
  Pf.lemAsAx (unfoldExcept T L p)

/-- The interface set: the least closed set of names for the library of the interface that
contains the constants of the statement and the axioms and laws that the proof uses. -/
def ifaceSet (T C : Name → Bool) (L : Lib) (p : Pf) (l r : Tm) : List Name :=
  close (ifaceBase T C L) (l.consts ++ r.consts ++ (ifaceProof T L p).axRefs)

/-- The interface surface. -/
def ifaceLib (T C : Name → Bool) (L : Lib) (p : Pf) (l r : Tm) : Lib :=
  restrict (fun n => (ifaceSet T C L p l r).contains n) (ifaceBase T C L)

/-- The proof over the interface surface. -/
def ifacePf (T C : Name → Bool) (L : Lib) (p : Pf) (l r : Tm) : Pf :=
  inlineDefs (fun n => (ifaceSet T C L p l r).contains n) (ifaceBase T C L) (ifaceProof T L p)

theorem ifaceBase_noThm (T C : Name → Bool) (L : Lib) : ∀ e ∈ ifaceBase T C L, e.isThm = false :=
  fun e he => lawsAsAxioms_noThm _ e (List.mem_filter.mp he).1

theorem ifaceBase_wf {L : Lib} (hwf : WF L) (T C : Name → Bool) : WF (ifaceBase T C L) :=
  (WF.keepLawsAsAxioms (T := T) hwf).filter_noThm (Entry.notSubject C) (by
    intro e he
    cases e with
    | defn _ _ => rfl
    | axm _ _ _ => rfl
    | thm _ _ _ _ => simp [Entry.notSubject] at he)

/-- Theorem 4.2 (interface soundness). Let the proof, with the theorems outside the laws
inlined, unfold no subject. Then its statement is derivable from the interface surface. -/
theorem interface_surface {L : Lib} (hwf : WF L) {p : Pf} {l r : Tm} (hc : Chk L p l r)
    (T C : Name → Bool) (hseal : ∀ c ∈ (unfoldExcept T L p).deltaRefs, C c = false) :
    Chk (ifaceLib T C L p l r) (ifacePf T C L p l r) l r := by
  have h1 : Chk (keepLaws T L) (unfoldExcept T L p) l r := by
    have := lemma_elim_except (T := T) hwf [] p l r (by intro e he; cases he) (by simpa using hc)
    simpa using this
  have h3 : Chk (ifaceBase T C L) (ifaceProof T L p) l r :=
    h1.lemAsAx.dropSubjects (lawsAsAxioms_noThm _) (by
      intro c hcm
      rw [Pf.deltaRefs_lemAsAx] at hcm
      exact hseal c hcm)
  have hwfB := ifaceBase_wf hwf T C
  have h4 := def_elim (S := fun n => (ifaceSet T C L p l r).contains n) (l := l) (r := r)
    (by
      intro d hd
      exact contains_of_mem (close_sub _ _ _ (List.mem_append_left _ (List.mem_append_left _ hd))))
    (by
      intro d hd
      exact contains_of_mem (close_sub _ _ _ (List.mem_append_left _ (List.mem_append_right _ hd))))
    hwfB (ifaceBase_noThm T C L)
    (by
      intro e he hk d hd
      have hnt := ifaceBase_noThm T C L e he
      have hname : e.name ∈ ifaceSet T C L p l r := by
        cases e with
        | defn c u => exact mem_of_contains hk
        | axm a l r => exact mem_of_contains hk
        | thm _ _ _ _ => simp [Entry.kept] at hk
      exact contains_of_mem (close_closed _ hwfB _ e he hnt hname d hd))
    [] (ifaceProof T L p) (by intro e he; cases he) (by intro e he; cases he)
    (by
      intro a ha
      exact contains_of_mem (close_sub _ _ _ (List.mem_append_right _ ha)))
    (by simpa using h3)
  simpa [ifaceLib, ifacePf] using h4

/-- The interface surface is a well-formed library without theorems. -/
theorem ifaceLib_wf {L : Lib} (hwf : WF L) (T C : Name → Bool) (p : Pf) (l r : Tm) :
    WF (ifaceLib T C L p l r) :=
  restrict_wf (ifaceBase_wf hwf T C) _

/-- Proposition 4.3, first half: the interface surface defines no subject. -/
theorem ifaceLib_noSubject {T C : Name → Bool} {L : Lib} {p : Pf} {l r : Tm} {c : Name} {u : Tm}
    (hm : Entry.defn c u ∈ ifaceLib T C L p l r) : C c = false := by
  have h1 : Entry.defn c u ∈ ifaceBase T C L := (List.mem_filter.mp hm).1
  have h2 := (List.mem_filter.mp h1).2
  simpa [Entry.notSubject] using h2

/-- Proposition 4.3, second half: an entry of the interface surface is a definition or an
axiom of the library, or the statement of one of its laws. -/
theorem ifaceLib_entries {T C : Name → Bool} {L : Lib} {p : Pf} {l r : Tm} {e : Entry}
    (hm : e ∈ ifaceLib T C L p l r) :
    (e ∈ L ∧ e.isThm = false) ∨
      ∃ h s t q, e = Entry.axm h s t ∧ Entry.thm h s t q ∈ L ∧ T h = true := by
  have h1 : e ∈ ifaceBase T C L := (List.mem_filter.mp hm).1
  have h2 : e ∈ lawsAsAxioms (keepLaws T L) := (List.mem_filter.mp h1).1
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp h2
  have hin := (List.mem_filter.mp he0).1
  have hk := (List.mem_filter.mp he0).2
  cases e0 with
  | defn c u => exact Or.inl ⟨hin, rfl⟩
  | axm a s t => exact Or.inl ⟨hin, rfl⟩
  | thm h s t q => exact Or.inr ⟨h, s, t, q, rfl, hin, hk⟩

/-- With no law and no subject, the hypothesis of the theorem holds for every proof. -/
theorem no_subject_sealed (L : Lib) (p : Pf) :
    ∀ c ∈ (unfoldExcept (fun _ => false) L p).deltaRefs, (fun _ : Name => false) c = false :=
  fun _ _ => rfl

/-! ## Example (Section 4) -/

namespace LawExample
open Tm

abbrev nId : Name := 20
abbrev nTwice : Name := 21
abbrev nTwiceId : Name := 22
abbrev nClient : Name := 23

/-- `id := λx. x` -/
def idBody : Tm := lam (bvar 0)
/-- `twice := λf. λx. f (f x)` -/
def twiceBody : Tm := lam (lam (app (bvar 1) (app (bvar 1) (bvar 0))))
/-- `twice id` -/
def twiceId : Tm := app (const nTwice) (const nId)

def K1 : Lib := [Entry.defn nId idBody]
def K2 : Lib := Entry.defn nTwice twiceBody :: K1
/-- The law `twice_id : twice id ≐ id`, proved by unfolding `twice` and `id`. -/
def pLaw : Pf := joinPf K2 32 twiceId (const nId)
def K3 : Lib := Entry.thm nTwiceId twiceId (const nId) pLaw :: K2
/-- The client `twice id (twice id) ≐ twice id`, proved from the law and the body of `id`. -/
def pClient : Pf :=
  Pf.trans (Pf.app (Pf.lem nTwiceId) (Pf.refl twiceId))
    (Pf.trans (Pf.app (Pf.delta nId) (Pf.refl twiceId)) (Pf.beta (bvar 0) twiceId))
def K4 : Lib := Entry.thm nClient (app twiceId twiceId) twiceId pClient :: K3

def laws : Name → Bool := fun n => n == nTwiceId
def subjects : Name → Bool := fun n => n == nTwice

theorem K4_wf : WF K4 := wfb_sound K4 (by decide)

/-- The audit surface of the client, as in the first paper: the bodies of `twice` and `id`. -/
example : (auditLib K3 pClient (app twiceId twiceId) twiceId).map Entry.name = [nTwice, nId] := by
  decide

/-- The client unfolds no subject once the theorems outside the laws are inlined. -/
example : (unfoldExcept laws K3 pClient).deltaRefs.all (fun c => !subjects c) = true := by
  decide

/-- The interface surface of the client: the law `twice_id` and the body of `id`. -/
example : ifaceLib laws subjects K3 pClient (app twiceId twiceId) twiceId
    = [Entry.axm nTwiceId twiceId (const nId), Entry.defn nId idBody] := by
  decide

/-- The proof over the interface surface is accepted by the kernel, as Theorem 4.2 says. -/
example : infer (ifaceLib laws subjects K3 pClient (app twiceId twiceId) twiceId)
    (ifacePf laws subjects K3 pClient (app twiceId twiceId) twiceId)
    = some (app twiceId twiceId, twiceId) := by
  decide

/-- A proof of the same statement that normalizes both sides unfolds the subject, so the
theorem does not apply to it. -/
example : (unfoldExcept laws K3 (joinPf K3 32 (app twiceId twiceId) twiceId)).deltaRefs.contains
    nTwice = true := by
  decide

end LawExample

end Audit

/-! The axioms the results depend on. -/
#print axioms Audit.lemma_elim_except
#print axioms Audit.interface_surface
#print axioms Audit.ifaceLib_wf
#print axioms Audit.ifaceLib_noSubject
#print axioms Audit.ifaceLib_entries
#print axioms Audit.LawExample.K4_wf
