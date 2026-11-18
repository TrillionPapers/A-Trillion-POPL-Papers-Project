/-
  Audit surfaces: the library calculus and its theorems.

  Lean 4, version pinned in `lean-toolchain`. Nothing is imported beyond the prelude.
  Section numbers refer to the paper.
-/

namespace Audit

abbrev Name := Nat

/-! ## Terms (Section 2) -/

/-- Untyped λ-terms with constants, in de Bruijn notation. -/
inductive Tm where
  | bvar (i : Nat) : Tm
  | const (c : Name) : Tm
  | app (f a : Tm) : Tm
  | lam (b : Tm) : Tm
  deriving DecidableEq, Repr

namespace Tm

/-- `lift d k t` adds `d` to every index of `t` that is at least `k`. -/
def lift (d : Nat) : Nat → Tm → Tm
  | k, bvar i => if i < k then bvar i else bvar (i + d)
  | _, const c => const c
  | k, app f a => app (lift d k f) (lift d k a)
  | k, lam b => lam (lift d (k + 1) b)

/-- `subst a k t` replaces index `k` of `t` by `a` and lowers the indices above `k`. -/
def subst (a : Tm) : Nat → Tm → Tm
  | k, bvar i => if i < k then bvar i else if i = k then lift k 0 a else bvar (i - 1)
  | _, const c => const c
  | k, app f x => app (subst a k f) (subst a k x)
  | k, lam b => lam (subst a (k + 1) b)

/-- The contractum of the β-redex `(λ b) a`. -/
def inst (b a : Tm) : Tm := subst a 0 b

/-- The constants of a term. -/
def consts : Tm → List Name
  | bvar _ => []
  | const c => [c]
  | app f a => consts f ++ consts a
  | lam b => consts b

/-- `closedAt n t`: every free index of `t` is below `n`. -/
def closedAt : Nat → Tm → Bool
  | n, bvar i => decide (i < n)
  | _, const _ => true
  | n, app f a => closedAt n f && closedAt n a
  | n, lam b => closedAt (n + 1) b

abbrev Closed (t : Tm) : Prop := closedAt 0 t = true

/-- `csub c u t` replaces the constant `c` by `u` in `t`. There is no lifting: `u` is closed
wherever this is used. -/
def csub (c : Name) (u : Tm) : Tm → Tm
  | bvar i => bvar i
  | const d => if d = c then u else const d
  | app f a => app (csub c u f) (csub c u a)
  | lam b => lam (csub c u b)

theorem lift_closedAt (d : Nat) (t : Tm) :
    ∀ (n k : Nat), closedAt n t = true → n ≤ k → lift d k t = t := by
  induction t with
  | bvar i =>
    intro n k h hk
    have hi : i < n := by simpa [closedAt] using h
    have hik : i < k := Nat.lt_of_lt_of_le hi hk
    simp [lift, hik]
  | const c => intro n k _ _; rfl
  | app f a ihf iha =>
    intro n k h hk
    have h' : closedAt n f = true ∧ closedAt n a = true := by simpa [closedAt] using h
    simp [lift, ihf n k h'.1 hk, iha n k h'.2 hk]
  | lam b ih =>
    intro n k h hk
    have h' : closedAt (n + 1) b = true := by simpa [closedAt] using h
    simp [lift, ih (n + 1) (k + 1) h' (Nat.succ_le_succ hk)]

theorem subst_closedAt (a : Tm) (t : Tm) :
    ∀ (n k : Nat), closedAt n t = true → n ≤ k → subst a k t = t := by
  induction t with
  | bvar i =>
    intro n k h hk
    have hi : i < n := by simpa [closedAt] using h
    have hik : i < k := Nat.lt_of_lt_of_le hi hk
    simp [subst, hik]
  | const c => intro n k _ _; rfl
  | app f x ihf ihx =>
    intro n k h hk
    have h' : closedAt n f = true ∧ closedAt n x = true := by simpa [closedAt] using h
    simp [subst, ihf n k h'.1 hk, ihx n k h'.2 hk]
  | lam b ih =>
    intro n k h hk
    have h' : closedAt (n + 1) b = true := by simpa [closedAt] using h
    simp [subst, ih (n + 1) (k + 1) h' (Nat.succ_le_succ hk)]

theorem csub_lift {c : Name} {u : Tm} (hu : Closed u) (d : Nat) (t : Tm) :
    ∀ (k : Nat), csub c u (lift d k t) = lift d k (csub c u t) := by
  induction t with
  | bvar i =>
    intro k
    by_cases h : i < k <;> simp [lift, csub, h]
  | const e =>
    intro k
    by_cases h : e = c
    · simp [lift, csub, h, lift_closedAt d u 0 k hu (Nat.zero_le k)]
    · simp [lift, csub, h]
  | app f a ihf iha => intro k; simp [lift, csub, ihf k, iha k]
  | lam b ih => intro k; simp [lift, csub, ih (k + 1)]

theorem csub_subst {c : Name} {u : Tm} (hu : Closed u) (a : Tm) (t : Tm) :
    ∀ (k : Nat), csub c u (subst a k t) = subst (csub c u a) k (csub c u t) := by
  induction t with
  | bvar i =>
    intro k
    by_cases h1 : i < k
    · simp [subst, csub, h1]
    · by_cases h2 : i = k
      · simp [subst, csub, h2, csub_lift hu]
      · simp [subst, csub, h1, h2]
  | const e =>
    intro k
    by_cases h : e = c
    · simp [subst, csub, h, subst_closedAt (csub c u a) u 0 k hu (Nat.zero_le k)]
    · simp [subst, csub, h]
  | app f x ihf ihx => intro k; simp [subst, csub, ihf k, ihx k]
  | lam b ih => intro k; simp [subst, csub, ih (k + 1)]

/-- Replacing a constant by a closed term commutes with β-instantiation. -/
theorem csub_inst {c : Name} {u : Tm} (hu : Closed u) (b a : Tm) :
    csub c u (inst b a) = inst (csub c u b) (csub c u a) :=
  csub_subst hu a b 0

theorem csub_of_not_mem {c : Name} {u : Tm} : ∀ (t : Tm), c ∉ consts t → csub c u t = t
  | bvar _, _ => rfl
  | const d, h => by
      have hd : d ≠ c := by
        intro e
        apply h
        simp [consts, e]
      simp [csub, hd]
  | app f a, h => by
      have hf : c ∉ consts f := fun m => h (by simp [consts, m])
      have ha : c ∉ consts a := fun m => h (by simp [consts, m])
      simp [csub, csub_of_not_mem f hf, csub_of_not_mem a ha]
  | lam b, h => by
      have hb : c ∉ consts b := fun m => h (by simpa [consts] using m)
      simp [csub, csub_of_not_mem b hb]

end Tm

/-! ## Proofs, entries, libraries (Section 2) -/

/-- Proof terms for equations between terms. -/
inductive Pf where
  | refl (t : Tm) : Pf
  | symm (p : Pf) : Pf
  | trans (p q : Pf) : Pf
  | app (p q : Pf) : Pf
  | lam (p : Pf) : Pf
  | beta (b a : Tm) : Pf
  | delta (c : Name) : Pf
  | ax (a : Name) : Pf
  | lem (h : Name) : Pf
  deriving DecidableEq, Repr

/-- A library entry: a definition, an axiom, or a theorem with its proof. -/
inductive Entry where
  | defn (c : Name) (body : Tm) : Entry
  | axm (a : Name) (l r : Tm) : Entry
  | thm (h : Name) (l r : Tm) (p : Pf) : Entry
  deriving DecidableEq, Repr

/-- A library lists its entries newest first. -/
abbrev Lib := List Entry

namespace Entry

def name : Entry → Name
  | defn c _ => c
  | axm a _ _ => a
  | thm h _ _ _ => h

/-- The constants of an entry's body or statement. Proofs do not count. -/
def consts : Entry → List Name
  | defn _ u => u.consts
  | axm _ l r => l.consts ++ r.consts
  | thm _ l r _ => l.consts ++ r.consts

def isThm : Entry → Bool
  | defn _ _ => false
  | axm _ _ _ => false
  | thm _ _ _ _ => true

end Entry

/-- `Chk L p l r`: the proof `p` establishes `l ≐ r` in the library `L`. -/
inductive Chk (L : Lib) : Pf → Tm → Tm → Prop where
  | refl (t : Tm) : Chk L (.refl t) t t
  | symm {p : Pf} {l r : Tm} : Chk L p l r → Chk L (.symm p) r l
  | trans {p q : Pf} {l m r : Tm} : Chk L p l m → Chk L q m r → Chk L (.trans p q) l r
  | app {p q : Pf} {f f' a a' : Tm} :
      Chk L p f f' → Chk L q a a' → Chk L (.app p q) (.app f a) (.app f' a')
  | lam {p : Pf} {b b' : Tm} : Chk L p b b' → Chk L (.lam p) (.lam b) (.lam b')
  | beta (b a : Tm) : Chk L (.beta b a) (.app (.lam b) a) (Tm.inst b a)
  | delta {c : Name} {u : Tm} : Entry.defn c u ∈ L → Chk L (.delta c) (.const c) u
  | ax {a : Name} {l r : Tm} : Entry.axm a l r ∈ L → Chk L (.ax a) l r
  | lem {h : Name} {l r : Tm} {q : Pf} : Entry.thm h l r q ∈ L → Chk L (.lem h) l r

/-- `n` is fresh for `L`: no entry of `L` has this name, and no body or statement mentions it. -/
def Fresh (n : Name) (L : Lib) : Prop := ∀ e ∈ L, e.name ≠ n ∧ n ∉ e.consts

/-- Well-formed libraries. A definition is closed and not recursive, every name is fresh
when it is introduced, and every theorem is checked against the entries before it. -/
inductive WF : Lib → Prop where
  | nil : WF []
  | defn {L : Lib} {c : Name} {u : Tm} :
      WF L → Fresh c L → Tm.Closed u → c ∉ u.consts → WF (Entry.defn c u :: L)
  | axm {L : Lib} {a : Name} {l r : Tm} : WF L → Fresh a L → WF (Entry.axm a l r :: L)
  | thm {L : Lib} {h : Name} {l r : Tm} {p : Pf} :
      WF L → Fresh h L → Chk L p l r → WF (Entry.thm h l r p :: L)

theorem WF.fresh_head {e : Entry} {L : Lib} (h : WF (e :: L)) : Fresh e.name L := by
  cases h <;> assumption

theorem WF.tail {e : Entry} {L : Lib} (h : WF (e :: L)) : WF L := by
  cases h <;> assumption

theorem Fresh.sub {n : Name} {L L' : Lib} (h : Fresh n L) (hsub : ∀ e ∈ L', e ∈ L) :
    Fresh n L' :=
  fun e he => h e (hsub e he)

theorem mem_mid {α : Type} {x e : α} {D L : List α} :
    x ∈ D ++ e :: L ↔ x = e ∨ x ∈ D ++ L := by
  simp only [List.mem_append, List.mem_cons]
  constructor
  · rintro (h | h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

namespace Pf

/-- The axioms a proof refers to directly. -/
def axRefs : Pf → List Name
  | refl _ => []
  | symm p => axRefs p
  | trans p q => axRefs p ++ axRefs q
  | app p q => axRefs p ++ axRefs q
  | lam p => axRefs p
  | beta _ _ => []
  | delta _ => []
  | ax a => [a]
  | lem _ => []

/-- The theorems a proof refers to directly. -/
def lemRefs : Pf → List Name
  | refl _ => []
  | symm p => lemRefs p
  | trans p q => lemRefs p ++ lemRefs q
  | app p q => lemRefs p ++ lemRefs q
  | lam p => lemRefs p
  | beta _ _ => []
  | delta _ => []
  | ax _ => []
  | lem h => [h]

/-- The definitions a proof unfolds. -/
def deltaRefs : Pf → List Name
  | refl _ => []
  | symm p => deltaRefs p
  | trans p q => deltaRefs p ++ deltaRefs q
  | app p q => deltaRefs p ++ deltaRefs q
  | lam p => deltaRefs p
  | beta _ _ => []
  | delta c => [c]
  | ax _ => []
  | lem _ => []

/-- Replace the constant `c` by `u` throughout a proof. Unfolding `c` becomes reflexivity. -/
def csub (c : Name) (u : Tm) : Pf → Pf
  | refl t => refl (Tm.csub c u t)
  | symm p => symm (csub c u p)
  | trans p q => trans (csub c u p) (csub c u q)
  | app p q => app (csub c u p) (csub c u q)
  | lam p => lam (csub c u p)
  | beta b a => beta (Tm.csub c u b) (Tm.csub c u a)
  | delta d => if d = c then refl u else delta d
  | ax a => ax a
  | lem h => lem h

/-- Replace every use of the theorem `h` by the proof `q`. -/
def inlineLem (h : Name) (q : Pf) : Pf → Pf
  | refl t => refl t
  | symm p => symm (inlineLem h q p)
  | trans p p' => trans (inlineLem h q p) (inlineLem h q p')
  | app p p' => app (inlineLem h q p) (inlineLem h q p')
  | lam p => lam (inlineLem h q p)
  | beta b a => beta b a
  | delta c => delta c
  | ax a => ax a
  | lem h' => if h' = h then q else lem h'

theorem axRefs_csub (c : Name) (u : Tm) (p : Pf) : (Pf.csub c u p).axRefs = p.axRefs := by
  induction p with
  | refl t => rfl
  | symm p ih => simpa [csub, axRefs] using ih
  | trans p q ihp ihq => simp [csub, axRefs, ihp, ihq]
  | app p q ihp ihq => simp [csub, axRefs, ihp, ihq]
  | lam p ih => simpa [csub, axRefs] using ih
  | beta b a => rfl
  | delta d => by_cases h : d = c <;> simp [csub, axRefs, h]
  | ax a => rfl
  | lem h => rfl

end Pf

/-! ## Structural properties of checking (Section 2) -/

/-- Lemma 2.1 (locality): checking a proof consults the library only at the entries the proof
refers to, and at a theorem only for its statement. -/
theorem Chk.mono_refs {L L' : Lib} {p : Pf} {l r : Tm} (hc : Chk L p l r) :
    (∀ d u, d ∈ p.deltaRefs → Entry.defn d u ∈ L → Entry.defn d u ∈ L') →
    (∀ a l r, a ∈ p.axRefs → Entry.axm a l r ∈ L → Entry.axm a l r ∈ L') →
    (∀ h l r q, h ∈ p.lemRefs → Entry.thm h l r q ∈ L → ∃ q', Entry.thm h l r q' ∈ L') →
    Chk L' p l r := by
  induction hc with
  | refl t => intro _ _ _; exact Chk.refl t
  | symm _ ih => intro hd ha hl; exact Chk.symm (ih hd ha hl)
  | trans _ _ ih1 ih2 =>
    intro hd ha hl
    exact Chk.trans
      (ih1 (fun d u m => hd d u (List.mem_append_left _ m))
           (fun a l r m => ha a l r (List.mem_append_left _ m))
           (fun h l r q m => hl h l r q (List.mem_append_left _ m)))
      (ih2 (fun d u m => hd d u (List.mem_append_right _ m))
           (fun a l r m => ha a l r (List.mem_append_right _ m))
           (fun h l r q m => hl h l r q (List.mem_append_right _ m)))
  | app _ _ ih1 ih2 =>
    intro hd ha hl
    exact Chk.app
      (ih1 (fun d u m => hd d u (List.mem_append_left _ m))
           (fun a l r m => ha a l r (List.mem_append_left _ m))
           (fun h l r q m => hl h l r q (List.mem_append_left _ m)))
      (ih2 (fun d u m => hd d u (List.mem_append_right _ m))
           (fun a l r m => ha a l r (List.mem_append_right _ m))
           (fun h l r q m => hl h l r q (List.mem_append_right _ m)))
  | lam _ ih => intro hd ha hl; exact Chk.lam (ih hd ha hl)
  | beta b a => intro _ _ _; exact Chk.beta b a
  | delta hm => intro hd _ _; exact Chk.delta (hd _ _ (List.Mem.head _) hm)
  | ax hm => intro _ ha _; exact Chk.ax (ha _ _ _ (List.Mem.head _) hm)
  | lem hm =>
    intro _ _ hl
    obtain ⟨q', hq'⟩ := hl _ _ _ _ (List.Mem.head _) hm
    exact Chk.lem hq'

/-- Lemma 2.1, second part (weakening): a proof checked in a library is checked in every
library that contains its entries. -/
theorem Chk.weaken {L L' : Lib} {p : Pf} {l r : Tm} (hc : Chk L p l r)
    (hsub : ∀ e ∈ L, e ∈ L') : Chk L' p l r :=
  hc.mono_refs (fun _ _ _ m => hsub _ m) (fun _ _ _ _ m => hsub _ m)
    (fun _ _ _ q _ m => ⟨q, hsub _ m⟩)

/-- Cut: a use of a theorem can be replaced by a proof of its statement. -/
theorem Chk.inlineLem {L L' : Lib} {h : Name} {l0 r0 : Tm} {q : Pf}
    (huniq : ∀ l r q', Entry.thm h l r q' ∈ L → l = l0 ∧ r = r0)
    (hq : Chk L' q l0 r0)
    (hdef : ∀ d u, Entry.defn d u ∈ L → Entry.defn d u ∈ L')
    (hax : ∀ a l r, Entry.axm a l r ∈ L → Entry.axm a l r ∈ L')
    (hthm : ∀ h' l r q', Entry.thm h' l r q' ∈ L → h' ≠ h → Entry.thm h' l r q' ∈ L')
    {p : Pf} {l r : Tm} (hc : Chk L p l r) : Chk L' (Pf.inlineLem h q p) l r := by
  induction hc with
  | refl t => exact Chk.refl t
  | symm _ ih => exact Chk.symm ih
  | trans _ _ ih1 ih2 => exact Chk.trans ih1 ih2
  | app _ _ ih1 ih2 => exact Chk.app ih1 ih2
  | lam _ ih => exact Chk.lam ih
  | beta b a => exact Chk.beta b a
  | delta hm => exact Chk.delta (hdef _ _ hm)
  | ax hm => exact Chk.ax (hax _ _ _ hm)
  | @lem h' l r q' hm =>
    by_cases e : h' = h
    · have hlr := huniq l r q' (e ▸ hm)
      have e1 : Pf.inlineLem h q (Pf.lem h') = q := by simp [Pf.inlineLem, e]
      rw [e1, hlr.1, hlr.2]
      exact hq
    · have e1 : Pf.inlineLem h q (Pf.lem h') = Pf.lem h' := by simp [Pf.inlineLem, e]
      rw [e1]
      exact Chk.lem (hthm _ _ _ _ hm e)

/-- Definition elimination: replacing a defined constant by its body maps proofs to proofs. -/
theorem Chk.csub {L L' : Lib} {c : Name} {u : Tm} (hu : Tm.Closed u) (hcu : c ∉ u.consts)
    (hdef : ∀ d v, Entry.defn d v ∈ L →
      (d = c ∧ v = u) ∨ (d ≠ c ∧ Entry.defn d v ∈ L' ∧ c ∉ v.consts))
    (hax : ∀ a l r, Entry.axm a l r ∈ L → Entry.axm a l r ∈ L' ∧ c ∉ l.consts ∧ c ∉ r.consts)
    (hthm : ∀ e ∈ L, e.isThm = false)
    {p : Pf} {l r : Tm} (hc : Chk L p l r) :
    Chk L' (Pf.csub c u p) (Tm.csub c u l) (Tm.csub c u r) := by
  induction hc with
  | refl t => exact Chk.refl _
  | symm _ ih => exact Chk.symm ih
  | trans _ _ ih1 ih2 => exact Chk.trans ih1 ih2
  | app _ _ ih1 ih2 => exact Chk.app ih1 ih2
  | lam _ ih => exact Chk.lam ih
  | beta b a =>
    have e1 : Pf.csub c u (Pf.beta b a) = Pf.beta (Tm.csub c u b) (Tm.csub c u a) := rfl
    have e2 : Tm.csub c u (Tm.app (Tm.lam b) a)
        = Tm.app (Tm.lam (Tm.csub c u b)) (Tm.csub c u a) := rfl
    rw [e1, e2, Tm.csub_inst hu]
    exact Chk.beta _ _
  | @delta d v hm =>
    rcases hdef d v hm with h | h
    · obtain ⟨hd, hv⟩ := h
      have e1 : Pf.csub c u (Pf.delta d) = Pf.refl u := by simp [Pf.csub, hd]
      have e2 : Tm.csub c u (Tm.const d) = u := by simp [Tm.csub, hd]
      have e3 : Tm.csub c u v = u := by rw [hv]; exact Tm.csub_of_not_mem _ hcu
      rw [e1, e2, e3]
      exact Chk.refl u
    · obtain ⟨hne, hm', hnot⟩ := h
      have e1 : Pf.csub c u (Pf.delta d) = Pf.delta d := by simp [Pf.csub, hne]
      have e2 : Tm.csub c u (Tm.const d) = Tm.const d := by simp [Tm.csub, hne]
      rw [e1, e2, Tm.csub_of_not_mem _ hnot]
      exact Chk.delta hm'
  | @ax a l r hm =>
    obtain ⟨hm', hl, hr⟩ := hax a l r hm
    have e1 : Pf.csub c u (Pf.ax a) = Pf.ax a := rfl
    rw [e1, Tm.csub_of_not_mem _ hl, Tm.csub_of_not_mem _ hr]
    exact Chk.ax hm'
  | @lem h l r q hm =>
    have := hthm _ hm
    simp [Entry.isThm] at this

/-! ## Eliminating theorems (Section 3) -/

/-- Inline every theorem of the library into a proof, newest first. -/
def unfoldLems : Lib → Pf → Pf
  | [], p => p
  | Entry.defn _ _ :: L, p => unfoldLems L p
  | Entry.axm _ _ _ :: L, p => unfoldLems L p
  | Entry.thm h _ _ q :: L, p => unfoldLems L (Pf.inlineLem h q p)

/-- The library without its theorems. -/
def dropThms (L : Lib) : Lib := L.filter (fun e => !e.isThm)

theorem lemma_elim {L : Lib} (hwf : WF L) :
    ∀ (D : Lib) (p : Pf) (l r : Tm), (∀ e ∈ D, e.isThm = false) →
      Chk (D ++ L) p l r → Chk (D ++ dropThms L) (unfoldLems L p) l r := by
  induction hwf with
  | nil =>
    intro D p l r _ hc
    simpa [dropThms, unfoldLems] using hc
  | @defn L c u _ _ _ _ ih =>
    intro D p l r hD hc
    have hD' : ∀ e ∈ D ++ [Entry.defn c u], e.isThm = false := by
      intro e he
      rcases List.mem_append.mp he with h | h
      · exact hD e h
      · have : e = Entry.defn c u := by simpa using h
        rw [this]; rfl
    have := ih (D ++ [Entry.defn c u]) p l r hD' (by simpa using hc)
    simpa [dropThms, unfoldLems, Entry.isThm] using this
  | @axm L a l' r' _ _ ih =>
    intro D p l r hD hc
    have hD' : ∀ e ∈ D ++ [Entry.axm a l' r'], e.isThm = false := by
      intro e he
      rcases List.mem_append.mp he with h | h
      · exact hD e h
      · have : e = Entry.axm a l' r' := by simpa using h
        rw [this]; rfl
    have := ih (D ++ [Entry.axm a l' r']) p l r hD' (by simpa using hc)
    simpa [dropThms, unfoldLems, Entry.isThm] using this
  | @thm L h l' r' q _ hfresh hq ih =>
    intro D p l r hD hc
    have hc' : Chk (D ++ L) (Pf.inlineLem h q p) l r := by
      refine Chk.inlineLem (L := D ++ Entry.thm h l' r' q :: L) (l0 := l') (r0 := r')
        ?_ ?_ ?_ ?_ ?_ hc
      · intro l1 r1 q1 hm
        rcases mem_mid.mp hm with hm | hm
        · cases hm; exact ⟨rfl, rfl⟩
        · rcases List.mem_append.mp hm with hm | hm
          · have := hD _ hm
            simp [Entry.isThm] at this
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
    have := ih D _ l r hD hc'
    simpa [dropThms, unfoldLems, Entry.isThm] using this

/-! ## Eliminating definitions outside a set (Section 3) -/

/-- An entry is kept by a set of names when it is a definition or an axiom named in the set. -/
def Entry.kept (S : Name → Bool) : Entry → Bool
  | Entry.defn c _ => S c
  | Entry.axm a _ _ => S a
  | Entry.thm _ _ _ _ => false

/-- The definitions and axioms of a library that a set of names keeps. -/
def restrict (S : Name → Bool) (L : Lib) : Lib := L.filter (Entry.kept S)

/-- Inline every definition outside the set into a proof, newest first. -/
def inlineDefs (S : Name → Bool) : Lib → Pf → Pf
  | [], p => p
  | Entry.defn c u :: L, p =>
    if S c then inlineDefs S L p else inlineDefs S L (Pf.csub c u p)
  | Entry.axm _ _ _ :: L, p => inlineDefs S L p
  | Entry.thm _ _ _ _ :: L, p => inlineDefs S L p

theorem def_elim {S : Name → Bool} {l r : Tm}
    (hl : ∀ d ∈ l.consts, S d = true) (hr : ∀ d ∈ r.consts, S d = true)
    {L : Lib} (hwf : WF L) :
    (∀ e ∈ L, e.isThm = false) →
    (∀ e ∈ L, e.kept S = true → ∀ d ∈ e.consts, S d = true) →
    ∀ (D : Lib) (p : Pf),
      (∀ e ∈ D, e.kept S = true) → (∀ e ∈ D, ∀ d ∈ e.consts, S d = true) →
      (∀ a ∈ p.axRefs, S a = true) →
      Chk (D ++ L) p l r → Chk (D ++ restrict S L) (inlineDefs S L p) l r := by
  induction hwf with
  | nil =>
    intro _ _ D p _ _ _ hc
    simpa [restrict, inlineDefs] using hc
  | @defn L c u _ hfresh hclosed hcu ih =>
    intro hnt hcl D p hDk hDc hax hc
    have hnt' : ∀ e ∈ L, e.isThm = false := fun e he => hnt e (List.Mem.tail _ he)
    have hcl' : ∀ e ∈ L, e.kept S = true → ∀ d ∈ e.consts, S d = true :=
      fun e he => hcl e (List.Mem.tail _ he)
    by_cases hS : S c = true
    · have hDk' : ∀ e ∈ D ++ [Entry.defn c u], e.kept S = true := by
        intro e he
        rcases List.mem_append.mp he with h | h
        · exact hDk e h
        · have : e = Entry.defn c u := by simpa using h
          rw [this]; exact hS
      have hDc' : ∀ e ∈ D ++ [Entry.defn c u], ∀ d ∈ e.consts, S d = true := by
        intro e he
        rcases List.mem_append.mp he with h | h
        · exact hDc e h
        · have : e = Entry.defn c u := by simpa using h
          rw [this]; exact hcl _ (List.Mem.head _) hS
      have := ih hnt' hcl' (D ++ [Entry.defn c u]) p hDk' hDc' hax (by simpa using hc)
      simpa [restrict, inlineDefs, Entry.kept, hS] using this
    · have hSc : S c = false := by simpa using hS
      have hcl_ : c ∉ l.consts := fun m => by
        have := hl c m
        rw [hSc] at this
        cases this
      have hcr_ : c ∉ r.consts := fun m => by
        have := hr c m
        rw [hSc] at this
        cases this
      have hc' : Chk (D ++ L) (Pf.csub c u p) (Tm.csub c u l) (Tm.csub c u r) := by
        refine Chk.csub hclosed hcu ?_ ?_ ?_ hc
        · intro d v hm
          rcases mem_mid.mp hm with h | h
          · cases h; exact Or.inl ⟨rfl, rfl⟩
          · rcases List.mem_append.mp h with h | h
            · have hd : S d = true := hDk _ h
              refine Or.inr ⟨?_, List.mem_append_left _ h, ?_⟩
              · intro e
                rw [e, hSc] at hd
                cases hd
              · intro m
                have := hDc _ h c m
                rw [hSc] at this
                cases this
            · have hf := hfresh _ h
              exact Or.inr ⟨hf.1, List.mem_append_right _ h, hf.2⟩
        · intro a l1 r1 hm
          rcases mem_mid.mp hm with h | h
          · cases h
          · rcases List.mem_append.mp h with h | h
            · refine ⟨List.mem_append_left _ h, ?_, ?_⟩
              · intro m
                have := hDc _ h c (List.mem_append_left _ m)
                rw [hSc] at this
                cases this
              · intro m
                have := hDc _ h c (List.mem_append_right _ m)
                rw [hSc] at this
                cases this
            · have hf := hfresh _ h
              exact ⟨List.mem_append_right _ h,
                fun m => hf.2 (List.mem_append_left _ m),
                fun m => hf.2 (List.mem_append_right _ m)⟩
        · intro e he
          rcases mem_mid.mp he with h | h
          · rw [h]; rfl
          · rcases List.mem_append.mp h with h | h
            · have hk := hDk _ h
              cases e with
              | defn _ _ => rfl
              | axm _ _ _ => rfl
              | thm _ _ _ _ => simp [Entry.kept] at hk
            · exact hnt' _ h
      rw [Tm.csub_of_not_mem _ hcl_, Tm.csub_of_not_mem _ hcr_] at hc'
      have := ih hnt' hcl' D (Pf.csub c u p) hDk hDc
        (by rw [Pf.axRefs_csub]; exact hax) hc'
      simpa [restrict, inlineDefs, Entry.kept, hSc] using this
  | @axm L a l1 r1 _ hfresh ih =>
    intro hnt hcl D p hDk hDc hax hc
    have hnt' : ∀ e ∈ L, e.isThm = false := fun e he => hnt e (List.Mem.tail _ he)
    have hcl' : ∀ e ∈ L, e.kept S = true → ∀ d ∈ e.consts, S d = true :=
      fun e he => hcl e (List.Mem.tail _ he)
    by_cases hS : S a = true
    · have hDk' : ∀ e ∈ D ++ [Entry.axm a l1 r1], e.kept S = true := by
        intro e he
        rcases List.mem_append.mp he with h | h
        · exact hDk e h
        · have : e = Entry.axm a l1 r1 := by simpa using h
          rw [this]; exact hS
      have hDc' : ∀ e ∈ D ++ [Entry.axm a l1 r1], ∀ d ∈ e.consts, S d = true := by
        intro e he
        rcases List.mem_append.mp he with h | h
        · exact hDc e h
        · have : e = Entry.axm a l1 r1 := by simpa using h
          rw [this]; exact hcl _ (List.Mem.head _) hS
      have := ih hnt' hcl' (D ++ [Entry.axm a l1 r1]) p hDk' hDc' hax (by simpa using hc)
      simpa [restrict, inlineDefs, Entry.kept, hS] using this
    · have hSa : S a = false := by simpa using hS
      have hc' : Chk (D ++ L) p l r := by
        refine hc.mono_refs ?_ ?_ ?_
        · intro d u _ hm
          rcases mem_mid.mp hm with h | h
          · cases h
          · exact h
        · intro a' l2 r2 hmem hm
          rcases mem_mid.mp hm with h | h
          · cases h
            have := hax _ hmem
            rw [hSa] at this
            cases this
          · exact h
        · intro h' l2 r2 q' _ hm
          rcases mem_mid.mp hm with h | h
          · cases h
          · exact ⟨q', h⟩
      have := ih hnt' hcl' D p hDk hDc hax hc'
      simpa [restrict, inlineDefs, Entry.kept, hSa] using this
  | @thm L h l1 r1 q _ _ _ ih =>
    intro hnt
    have := hnt _ (List.Mem.head _)
    simp [Entry.isThm] at this

/-- A sublibrary without theorems is well formed. -/
theorem WF.filter_noThm {L : Lib} (hwf : WF L) (f : Entry → Bool)
    (hf : ∀ e, f e = true → e.isThm = false) : WF (L.filter f) := by
  induction hwf with
  | nil => exact WF.nil
  | @defn L c u _ hfresh hcl hcu ih =>
    by_cases h : f (Entry.defn c u) = true
    · rw [List.filter_cons_of_pos h]
      exact WF.defn ih (hfresh.sub (fun e he => (List.mem_filter.mp he).1)) hcl hcu
    · rw [List.filter_cons_of_neg h]
      exact ih
  | @axm L a l r _ hfresh ih =>
    by_cases h : f (Entry.axm a l r) = true
    · rw [List.filter_cons_of_pos h]
      exact WF.axm ih (hfresh.sub (fun e he => (List.mem_filter.mp he).1))
    · rw [List.filter_cons_of_neg h]
      exact ih
  | @thm L h' l r p _ _ _ ih =>
    have h : ¬ f (Entry.thm h' l r p) = true := by
      intro hfe
      have := hf _ hfe
      simp [Entry.isThm] at this
    rw [List.filter_cons_of_neg h]
    exact ih

theorem restrict_dropThms (S : Name → Bool) (L : Lib) :
    restrict S (dropThms L) = restrict S L := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    unfold restrict at ih ⊢
    cases e with
    | defn c u =>
      have e1 : dropThms (Entry.defn c u :: L) = Entry.defn c u :: dropThms L := rfl
      rw [e1]
      by_cases h : S c = true
      · have hk : Entry.kept S (Entry.defn c u) = true := h
        rw [List.filter_cons_of_pos hk, List.filter_cons_of_pos hk, ih]
      · have hk : ¬ Entry.kept S (Entry.defn c u) = true := h
        rw [List.filter_cons_of_neg hk, List.filter_cons_of_neg hk, ih]
    | axm a l r =>
      have e1 : dropThms (Entry.axm a l r :: L) = Entry.axm a l r :: dropThms L := rfl
      rw [e1]
      by_cases h : S a = true
      · have hk : Entry.kept S (Entry.axm a l r) = true := h
        rw [List.filter_cons_of_pos hk, List.filter_cons_of_pos hk, ih]
      · have hk : ¬ Entry.kept S (Entry.axm a l r) = true := h
        rw [List.filter_cons_of_neg hk, List.filter_cons_of_neg hk, ih]
    | thm h l r p =>
      have e1 : dropThms (Entry.thm h l r p :: L) = dropThms L := rfl
      have hk : ¬ Entry.kept S (Entry.thm h l r p) = true := by simp [Entry.kept]
      rw [e1, ih, List.filter_cons_of_neg hk]

/-- The restriction of a well-formed library to a set of names is well formed (Theorem 3.4). -/
theorem restrict_wf {L : Lib} (hwf : WF L) (S : Name → Bool) : WF (restrict S L) :=
  hwf.filter_noThm _ (by
    intro e hk
    cases e with
    | defn _ _ => rfl
    | axm _ _ _ => rfl
    | thm _ _ _ _ => simp [Entry.kept] at hk)

/-- The restriction of a library to a set of names contains no theorem (Theorem 3.4). -/
theorem restrict_noThm {L : Lib} (S : Name → Bool) : ∀ e ∈ restrict S L, e.isThm = false := by
  intro e he
  have hk := (List.mem_filter.mp he).2
  cases e with
  | defn _ _ => rfl
  | axm _ _ _ => rfl
  | thm _ _ _ _ => simp [Entry.kept] at hk

/-- Audit soundness, stated with the axioms of the proof in which every theorem is inlined.
Theorem 3.4 is `audit_sound_usedAx` below, which follows from this. -/
theorem audit_sound {L : Lib} (hwf : WF L) {p : Pf} {l r : Tm} (hc : Chk L p l r)
    (S : Name → Bool)
    (hl : ∀ d ∈ l.consts, S d = true) (hr : ∀ d ∈ r.consts, S d = true)
    (hax : ∀ a ∈ (unfoldLems L p).axRefs, S a = true)
    (hcl : ∀ e ∈ L, e.kept S = true → ∀ d ∈ e.consts, S d = true) :
    Chk (restrict S L) (inlineDefs S (dropThms L) (unfoldLems L p)) l r := by
  have h1 : Chk (dropThms L) (unfoldLems L p) l r := by
    have := lemma_elim hwf [] p l r (by intro e he; cases he) (by simpa using hc)
    simpa using this
  have hwf' : WF (dropThms L) :=
    hwf.filter_noThm _ (by intro e he; simpa using he)
  have h2 := def_elim hl hr hwf'
    (by intro e he; simpa using (List.mem_filter.mp he).2)
    (fun e he => hcl e (List.mem_filter.mp he).1)
    [] (unfoldLems L p) (by intro e he; cases he) (by intro e he; cases he) hax
    (by simpa using h1)
  simpa [restrict_dropThms] using h2

/-! ## The audit surface (Section 3) -/

/-- One pass over the library, newest entry first. A definition or an axiom whose name has
been reached adds the constants of its body or statement. -/
def close : Lib → List Name → List Name
  | [], acc => acc
  | e :: L, acc =>
    if !e.isThm && acc.contains e.name then close L (e.consts ++ acc) else close L acc

theorem contains_of_mem {n : Name} {xs : List Name} (h : n ∈ xs) : xs.contains n = true := by
  simpa using h

theorem mem_of_contains {n : Name} {xs : List Name} (h : xs.contains n = true) : n ∈ xs := by
  simpa using h

theorem close_cons_pos {e : Entry} {L : Lib} {acc : List Name}
    (h : (!e.isThm && acc.contains e.name) = true) :
    close (e :: L) acc = close L (e.consts ++ acc) := by
  simp only [close, h, ↓reduceIte]

theorem close_cons_neg {e : Entry} {L : Lib} {acc : List Name}
    (h : ¬ (!e.isThm && acc.contains e.name) = true) :
    close (e :: L) acc = close L acc := by
  simp only [close]
  split
  · rename_i hc
    exact absurd hc h
  · rfl

/-! ## The axioms a proof uses (Section 3) -/

/-- One pass over the library, newest entry first. `lems` holds the theorems reached so far
and `axs` the axioms collected so far. A reached theorem adds what its proof refers to. -/
def reach : Lib → List Name → List Name → List Name
  | [], _, axs => axs
  | Entry.defn _ _ :: L, lems, axs => reach L lems axs
  | Entry.axm _ _ _ :: L, lems, axs => reach L lems axs
  | Entry.thm h _ _ q :: L, lems, axs =>
    if lems.contains h then reach L (q.lemRefs ++ lems) (q.axRefs ++ axs) else reach L lems axs

/-- The axioms that a proof uses, directly or through the theorems of the library. -/
def usedAx (L : Lib) (p : Pf) : List Name := reach L p.lemRefs p.axRefs

theorem reach_thm_pos {h : Name} {l r : Tm} {q : Pf} {L : Lib} {lems axs : List Name}
    (hc : lems.contains h = true) :
    reach (Entry.thm h l r q :: L) lems axs = reach L (q.lemRefs ++ lems) (q.axRefs ++ axs) := by
  simp only [reach, hc, ↓reduceIte]

theorem reach_thm_neg {h : Name} {l r : Tm} {q : Pf} {L : Lib} {lems axs : List Name}
    (hc : ¬ lems.contains h = true) :
    reach (Entry.thm h l r q :: L) lems axs = reach L lems axs := by
  simp only [reach]
  split
  · rename_i hc'
    exact absurd hc' hc
  · rfl

theorem reach_mono (L : Lib) : ∀ (lems lems' axs axs' : List Name),
    (∀ h ∈ lems, h ∈ lems') → (∀ a ∈ axs, a ∈ axs') →
    ∀ a ∈ reach L lems axs, a ∈ reach L lems' axs' := by
  induction L with
  | nil => intro lems lems' axs axs' _ ha a h; exact ha a h
  | cons e L ih =>
    intro lems lems' axs axs' hl ha a h
    cases e with
    | defn c u => exact ih lems lems' axs axs' hl ha a h
    | axm b l r => exact ih lems lems' axs axs' hl ha a h
    | thm g l r q =>
      have hl2 : ∀ x ∈ q.lemRefs ++ lems, x ∈ q.lemRefs ++ lems' := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact List.mem_append_left _ hx
        · exact List.mem_append_right _ (hl x hx)
      have ha2 : ∀ x ∈ q.axRefs ++ axs, x ∈ q.axRefs ++ axs' := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact List.mem_append_left _ hx
        · exact List.mem_append_right _ (ha x hx)
      by_cases hc : lems.contains g = true
      · have hc' : lems'.contains g = true := contains_of_mem (hl g (mem_of_contains hc))
        rw [reach_thm_pos hc] at h
        rw [reach_thm_pos hc']
        exact ih _ _ _ _ hl2 ha2 a h
      · rw [reach_thm_neg hc] at h
        by_cases hc' : lems'.contains g = true
        · rw [reach_thm_pos hc']
          exact ih _ _ _ _ (fun x hx => List.mem_append_right _ (hl x hx))
            (fun x hx => List.mem_append_right _ (ha x hx)) a h
        · rw [reach_thm_neg hc']
          exact ih _ _ _ _ hl ha a h

theorem Pf.inlineLem_of_not_mem (h : Name) (q : Pf) :
    ∀ (p : Pf), h ∉ p.lemRefs → Pf.inlineLem h q p = p := by
  intro p
  induction p with
  | refl t => intro _; rfl
  | symm p ih => intro hn; simp [Pf.inlineLem, ih hn]
  | trans p p' ihp ihp' =>
    intro hn
    have h1 : h ∉ p.lemRefs := fun m => hn (List.mem_append_left _ m)
    have h2 : h ∉ p'.lemRefs := fun m => hn (List.mem_append_right _ m)
    simp [Pf.inlineLem, ihp h1, ihp' h2]
  | app p p' ihp ihp' =>
    intro hn
    have h1 : h ∉ p.lemRefs := fun m => hn (List.mem_append_left _ m)
    have h2 : h ∉ p'.lemRefs := fun m => hn (List.mem_append_right _ m)
    simp [Pf.inlineLem, ihp h1, ihp' h2]
  | lam p ih => intro hn; simp [Pf.inlineLem, ih hn]
  | beta b a => intro _; rfl
  | delta c => intro _; rfl
  | ax a => intro _; rfl
  | lem g =>
    intro hn
    have hne : g ≠ h := fun e => hn (by rw [e]; exact List.Mem.head _)
    simp [Pf.inlineLem, hne]

theorem Pf.axRefs_inlineLem_sub (h : Name) (q : Pf) :
    ∀ (p : Pf), ∀ a ∈ (Pf.inlineLem h q p).axRefs, a ∈ p.axRefs ∨ a ∈ q.axRefs := by
  intro p
  induction p with
  | refl t => intro a ha; cases ha
  | symm p ih => intro a ha; exact ih a ha
  | trans p p' ihp ihp' =>
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · rcases ihp a ha with h1 | h1
      · exact Or.inl (List.mem_append_left _ h1)
      · exact Or.inr h1
    · rcases ihp' a ha with h1 | h1
      · exact Or.inl (List.mem_append_right _ h1)
      · exact Or.inr h1
  | app p p' ihp ihp' =>
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · rcases ihp a ha with h1 | h1
      · exact Or.inl (List.mem_append_left _ h1)
      · exact Or.inr h1
    · rcases ihp' a ha with h1 | h1
      · exact Or.inl (List.mem_append_right _ h1)
      · exact Or.inr h1
  | lam p ih => intro a ha; exact ih a ha
  | beta b a' => intro a ha; cases ha
  | delta c => intro a ha; cases ha
  | ax a' => intro a ha; exact Or.inl ha
  | lem g =>
    intro a ha
    by_cases e : g = h
    · have e1 : Pf.inlineLem h q (Pf.lem g) = q := by simp [Pf.inlineLem, e]
      rw [e1] at ha
      exact Or.inr ha
    · have e1 : Pf.inlineLem h q (Pf.lem g) = Pf.lem g := by simp [Pf.inlineLem, e]
      rw [e1] at ha
      cases ha

theorem Pf.lemRefs_inlineLem_sub (h : Name) (q : Pf) :
    ∀ (p : Pf), ∀ g ∈ (Pf.inlineLem h q p).lemRefs, g ∈ p.lemRefs ∨ g ∈ q.lemRefs := by
  intro p
  induction p with
  | refl t => intro g hg; cases hg
  | symm p ih => intro g hg; exact ih g hg
  | trans p p' ihp ihp' =>
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · rcases ihp g hg with h1 | h1
      · exact Or.inl (List.mem_append_left _ h1)
      · exact Or.inr h1
    · rcases ihp' g hg with h1 | h1
      · exact Or.inl (List.mem_append_right _ h1)
      · exact Or.inr h1
  | app p p' ihp ihp' =>
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · rcases ihp g hg with h1 | h1
      · exact Or.inl (List.mem_append_left _ h1)
      · exact Or.inr h1
    · rcases ihp' g hg with h1 | h1
      · exact Or.inl (List.mem_append_right _ h1)
      · exact Or.inr h1
  | lam p ih => intro g hg; exact ih g hg
  | beta b a => intro g hg; cases hg
  | delta c => intro g hg; cases hg
  | ax a => intro g hg; cases hg
  | lem g' =>
    intro g hg
    by_cases e : g' = h
    · have e1 : Pf.inlineLem h q (Pf.lem g') = q := by simp [Pf.inlineLem, e]
      rw [e1] at hg
      exact Or.inr hg
    · have e1 : Pf.inlineLem h q (Pf.lem g') = Pf.lem g' := by simp [Pf.inlineLem, e]
      rw [e1] at hg
      exact Or.inl hg

/-- The axioms of the proof in which every theorem is inlined are among the axioms that the
proof uses. So the axioms can be collected without building the inlined proof, which can be
exponentially larger. -/
theorem axRefs_unfoldLems_sub : ∀ (L : Lib) (p : Pf),
    ∀ a ∈ (unfoldLems L p).axRefs, a ∈ usedAx L p := by
  intro L
  induction L with
  | nil => intro p a h; exact h
  | cons e L ih =>
    intro p a h
    cases e with
    | defn c u => exact ih p a h
    | axm b l r => exact ih p a h
    | thm g l r q =>
      have h' : a ∈ (unfoldLems L (Pf.inlineLem g q p)).axRefs := h
      have h1 : a ∈ reach L (Pf.inlineLem g q p).lemRefs (Pf.inlineLem g q p).axRefs :=
        ih _ a h'
      show a ∈ reach (Entry.thm g l r q :: L) p.lemRefs p.axRefs
      by_cases hc : p.lemRefs.contains g = true
      · rw [reach_thm_pos hc]
        refine reach_mono L _ _ _ _ ?_ ?_ a h1
        · intro x hx
          rcases Pf.lemRefs_inlineLem_sub g q p x hx with hx | hx
          · exact List.mem_append_right _ hx
          · exact List.mem_append_left _ hx
        · intro x hx
          rcases Pf.axRefs_inlineLem_sub g q p x hx with hx | hx
          · exact List.mem_append_right _ hx
          · exact List.mem_append_left _ hx
      · have hn : g ∉ p.lemRefs := fun m => hc (contains_of_mem m)
        rw [Pf.inlineLem_of_not_mem g q p hn] at h1
        rw [reach_thm_neg hc]
        exact h1

/-- Theorem 3.4 (audit soundness) for any closed set of names that contains the constants of
the statement and the axioms that the proof uses. -/
theorem audit_sound_usedAx {L : Lib} (hwf : WF L) {p : Pf} {l r : Tm} (hc : Chk L p l r)
    (S : Name → Bool)
    (hl : ∀ d ∈ l.consts, S d = true) (hr : ∀ d ∈ r.consts, S d = true)
    (hax : ∀ a ∈ usedAx L p, S a = true)
    (hcl : ∀ e ∈ L, e.kept S = true → ∀ d ∈ e.consts, S d = true) :
    Chk (restrict S L) (inlineDefs S (dropThms L) (unfoldLems L p)) l r :=
  audit_sound hwf hc S hl hr (fun a ha => hax a (axRefs_unfoldLems_sub L p a ha)) hcl

/-! ## Closed sets of names (Section 3) -/

theorem close_sub (L : Lib) : ∀ (acc : List Name) (n : Name), n ∈ acc → n ∈ close L acc := by
  induction L with
  | nil => intro acc n h; exact h
  | cons e L ih =>
    intro acc n h
    simp only [close]
    split
    · exact ih _ n (List.mem_append_right _ h)
    · exact ih _ n h

theorem close_origin (L : Lib) :
    ∀ (acc : List Name) (n : Name), n ∈ close L acc → n ∈ acc ∨ ∃ e ∈ L, n ∈ e.consts := by
  induction L with
  | nil => intro acc n h; exact Or.inl h
  | cons e L ih =>
    intro acc n h
    simp only [close] at h
    split at h
    · rcases ih _ n h with h | ⟨e', he', hn⟩
      · rcases List.mem_append.mp h with h | h
        · exact Or.inr ⟨e, List.Mem.head _, h⟩
        · exact Or.inl h
      · exact Or.inr ⟨e', List.Mem.tail _ he', hn⟩
    · rcases ih _ n h with h | ⟨e', he', hn⟩
      · exact Or.inl h
      · exact Or.inr ⟨e', List.Mem.tail _ he', hn⟩

/-- Proposition 3.3, first half: the pass computes a closed set. -/
theorem close_closed : ∀ (L : Lib), WF L → ∀ (acc : List Name) (e : Entry), e ∈ L →
    e.isThm = false → e.name ∈ close L acc → ∀ d ∈ e.consts, d ∈ close L acc := by
  intro L
  induction L with
  | nil => intro _ acc e he; cases he
  | cons e0 L ih =>
    intro hwf acc e he hnt hname d hd
    have hfresh := hwf.fresh_head
    have hwf' := hwf.tail
    rcases List.mem_cons.mp he with heq | he'
    · rw [heq] at hnt hname hd
      by_cases hin : acc.contains e0.name = true
      · have hcond : (!e0.isThm && acc.contains e0.name) = true := by
          rw [hnt, hin]; rfl
        rw [close_cons_pos hcond]
        exact close_sub L _ d (List.mem_append_left _ hd)
      · have hcond : ¬ (!e0.isThm && acc.contains e0.name) = true := by
          intro hc
          rw [hnt] at hc
          exact hin (by simpa using hc)
        rw [close_cons_neg hcond] at hname
        rcases close_origin L acc _ hname with h | ⟨e', he', hn⟩
        · exact absurd (contains_of_mem h) hin
        · exact absurd hn (hfresh e' he').2
    · have key : ∃ acc', close (e0 :: L) acc = close L acc' := by
        by_cases hc : (!e0.isThm && acc.contains e0.name) = true
        · exact ⟨_, close_cons_pos hc⟩
        · exact ⟨_, close_cons_neg hc⟩
      obtain ⟨acc', hacc'⟩ := key
      rw [hacc'] at hname ⊢
      exact ih hwf' acc' e he' hnt hname d hd

/-- Proposition 3.3, second half: the pass computes the least closed set that contains its
seed. That it contains the seed is `close_sub`. -/
theorem close_least (L : Lib) : ∀ (acc : List Name) (S : Name → Prop),
    (∀ n ∈ acc, S n) →
    (∀ e ∈ L, e.isThm = false → S e.name → ∀ d ∈ e.consts, S d) →
    ∀ n ∈ close L acc, S n := by
  induction L with
  | nil => intro acc S h _ n hn; exact h n hn
  | cons e L ih =>
    intro acc S hacc hcl n hn
    have hcl' : ∀ e' ∈ L, e'.isThm = false → S e'.name → ∀ d ∈ e'.consts, S d :=
      fun e' he' => hcl e' (List.Mem.tail _ he')
    by_cases hcond : (!e.isThm && acc.contains e.name) = true
    · rw [close_cons_pos hcond] at hn
      have hc : e.isThm = false ∧ e.name ∈ acc := by
        cases hthm : e.isThm with
        | true => rw [hthm] at hcond; cases hcond
        | false =>
          rw [hthm] at hcond
          exact ⟨rfl, mem_of_contains (by simpa using hcond)⟩
      refine ih _ S ?_ hcl' n hn
      intro m hm
      rcases List.mem_append.mp hm with h | h
      · exact hcl e (List.Mem.head _) hc.1 (hacc _ hc.2) m h
      · exact hacc m h
    · rw [close_cons_neg hcond] at hn
      exact ih _ S hacc hcl' n hn

/-- The audit set of a checked proof: the least set of names that contains the constants of
the statement and the axioms the proof uses, and is closed under bodies and axiom statements. -/
def auditSet (L : Lib) (p : Pf) (l r : Tm) : List Name :=
  close L (l.consts ++ r.consts ++ usedAx L p)

/-- The audit surface: the definitions and axioms named by the audit set. -/
def auditLib (L : Lib) (p : Pf) (l r : Tm) : Lib :=
  restrict (fun n => (auditSet L p l r).contains n) L

/-- The proof over the audit surface, obtained by inlining theorems and then the definitions
outside the audit set. -/
def auditPf (L : Lib) (p : Pf) (l r : Tm) : Pf :=
  inlineDefs (fun n => (auditSet L p l r).contains n) (dropThms L) (unfoldLems L p)

/-- Theorem 3.4 for the audit set: the statement of a checked proof is derivable from its
audit surface alone. -/
theorem audit_surface {L : Lib} (hwf : WF L) {p : Pf} {l r : Tm} (hc : Chk L p l r) :
    Chk (auditLib L p l r) (auditPf L p l r) l r := by
  refine audit_sound hwf hc _ ?_ ?_ ?_ ?_
  · intro d hd
    have : d ∈ auditSet L p l r :=
      close_sub _ _ _ (List.mem_append_left _ (List.mem_append_left _ hd))
    exact contains_of_mem this
  · intro d hd
    have : d ∈ auditSet L p l r :=
      close_sub _ _ _ (List.mem_append_left _ (List.mem_append_right _ hd))
    exact contains_of_mem this
  · intro a ha
    have : a ∈ auditSet L p l r :=
      close_sub _ _ _ (List.mem_append_right _ (axRefs_unfoldLems_sub L p a ha))
    exact contains_of_mem this
  · intro e he hk d hd
    have hnt : e.isThm = false := by
      cases e with
      | defn _ _ => rfl
      | axm _ _ _ => rfl
      | thm _ _ _ _ => simp [Entry.kept] at hk
    have hname : e.name ∈ auditSet L p l r := by
      cases e with
      | defn c u => exact mem_of_contains hk
      | axm a l r => exact mem_of_contains hk
      | thm _ _ _ _ => simp [Entry.kept] at hk
    exact contains_of_mem (close_closed L hwf _ e he hnt hname d hd)

/-- The audit surface is part of the library. -/
theorem auditLib_sub {L : Lib} {p : Pf} {l r : Tm} : ∀ e ∈ auditLib L p l r, e ∈ L :=
  fun _ he => (List.mem_filter.mp he).1

/-- The audit surface contains no theorem. -/
theorem auditLib_noThm {L : Lib} {p : Pf} {l r : Tm} :
    ∀ e ∈ auditLib L p l r, e.isThm = false := by
  intro e he
  have hk := (List.mem_filter.mp he).2
  cases e with
  | defn _ _ => rfl
  | axm _ _ _ => rfl
  | thm _ _ _ _ => simp [Entry.kept] at hk

/-- The audit surface is a well-formed library on its own. -/
theorem auditLib_wf {L : Lib} (hwf : WF L) {p : Pf} {l r : Tm} : WF (auditLib L p l r) :=
  hwf.filter_noThm _ (by
    intro e hk
    cases e with
    | defn _ _ => rfl
    | axm _ _ _ => rfl
    | thm _ _ _ _ => simp [Entry.kept] at hk)

/-! ## Portability and merging (Section 4) -/

/-- Corollary 4.1: every library that contains the audit surface proves the statement. -/
theorem portable {L : Lib} (hwf : WF L) {p : Pf} {l r : Tm} (hc : Chk L p l r)
    (L' : Lib) (hsub : ∀ e ∈ auditLib L p l r, e ∈ L') : Chk L' (auditPf L p l r) l r :=
  (audit_surface hwf hc).weaken hsub

/-- Theorem 4.2: two extensions of a library merge without rechecking when the names that
one introduces are fresh for the other. -/
theorem merge {L1 L2 L0 : Lib} (h1 : WF (L1 ++ L0)) (h2 : WF (L2 ++ L0))
    (hfresh : ∀ e ∈ L1, Fresh e.name L2) : WF (L1 ++ (L2 ++ L0)) := by
  induction L1 with
  | nil => simpa using h2
  | cons e L1 ih =>
    have h1' : WF (e :: (L1 ++ L0)) := h1
    have hsubL : ∀ e' ∈ L1 ++ L0, e' ∈ L1 ++ (L2 ++ L0) := by
      intro e' he'
      rcases List.mem_append.mp he' with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_append_right _ h)
    have hf : Fresh e.name (L1 ++ (L2 ++ L0)) := by
      intro e' he'
      rcases List.mem_append.mp he' with h | h
      · exact h1'.fresh_head e' (List.mem_append_left _ h)
      · rcases List.mem_append.mp h with h | h
        · exact hfresh e (List.Mem.head _) e' h
        · exact h1'.fresh_head e' (List.mem_append_right _ h)
    have ih' : WF (L1 ++ (L2 ++ L0)) :=
      ih h1'.tail (fun e' he' => hfresh e' (List.Mem.tail _ he'))
    show WF (e :: (L1 ++ (L2 ++ L0)))
    cases h1' with
    | defn _ _ hcl hcu => exact WF.defn ih' hf hcl hcu
    | axm _ _ => exact WF.axm ih' hf
    | thm _ _ hchk => exact WF.thm ih' hf (hchk.weaken hsubL)

/-! ## Replacement (Section 4) -/

/-- Two libraries have the same interface when they agree entry by entry, except that the
proofs of corresponding theorems may differ. -/
inductive SameIface : Lib → Lib → Prop where
  | nil : SameIface [] []
  | same (e : Entry) {M M' : Lib} : SameIface M M' → SameIface (e :: M) (e :: M')
  | thm (h : Name) (l r : Tm) (p p' : Pf) {M M' : Lib} :
      SameIface M M' → SameIface (Entry.thm h l r p :: M) (Entry.thm h l r p' :: M')

theorem SameIface.defn_mem {M M' : Lib} (hi : SameIface M M') {d : Name} {u : Tm} :
    Entry.defn d u ∈ M → Entry.defn d u ∈ M' := by
  induction hi with
  | nil => intro h; cases h
  | same e _ ih =>
    intro h
    rcases List.mem_cons.mp h with h | h
    · rw [h]; exact List.Mem.head _
    · exact List.Mem.tail _ (ih h)
  | thm h l r p p' _ ih =>
    intro hm
    rcases List.mem_cons.mp hm with hm | hm
    · cases hm
    · exact List.Mem.tail _ (ih hm)

theorem SameIface.axm_mem {M M' : Lib} (hi : SameIface M M') {a : Name} {l r : Tm} :
    Entry.axm a l r ∈ M → Entry.axm a l r ∈ M' := by
  induction hi with
  | nil => intro h; cases h
  | same e _ ih =>
    intro h
    rcases List.mem_cons.mp h with h | h
    · rw [h]; exact List.Mem.head _
    · exact List.Mem.tail _ (ih h)
  | thm h l' r' p p' _ ih =>
    intro hm
    rcases List.mem_cons.mp hm with hm | hm
    · cases hm
    · exact List.Mem.tail _ (ih hm)

theorem SameIface.thm_mem {M M' : Lib} (hi : SameIface M M') {h : Name} {l r : Tm} {q : Pf} :
    Entry.thm h l r q ∈ M → ∃ q', Entry.thm h l r q' ∈ M' := by
  induction hi with
  | nil => intro hm; cases hm
  | same e _ ih =>
    intro hm
    rcases List.mem_cons.mp hm with hm | hm
    · exact ⟨q, by rw [hm]; exact List.Mem.head _⟩
    · obtain ⟨q', hq'⟩ := ih hm
      exact ⟨q', List.Mem.tail _ hq'⟩
  | thm h0 l0 r0 p p' _ ih =>
    intro hm
    rcases List.mem_cons.mp hm with hm | hm
    · cases hm
      exact ⟨p', List.Mem.head _⟩
    · obtain ⟨q', hq'⟩ := ih hm
      exact ⟨q', List.Mem.tail _ hq'⟩

theorem SameIface.fresh {M M' : Lib} (hi : SameIface M M') {n : Name} :
    Fresh n M → Fresh n M' := by
  induction hi with
  | nil => intro h; exact h
  | same e _ ih =>
    intro hf e' he'
    rcases List.mem_cons.mp he' with h | h
    · rw [h]; exact hf e (List.Mem.head _)
    · exact ih (fun x hx => hf x (List.Mem.tail _ hx)) e' h
  | thm h l r p p' _ ih =>
    intro hf e' he'
    rcases List.mem_cons.mp he' with h' | h'
    · rw [h']; exact hf (Entry.thm h l r p) (List.Mem.head _)
    · exact ih (fun x hx => hf x (List.Mem.tail _ hx)) e' h'

/-- Theorem 4.3: let the entries `L1` never unfold the definition `c`. Then the body of `c`
and the proofs between `c` and `L1` can be replaced without rechecking `L1`. -/
theorem replace {L1 M M' L0 : Lib} {c : Name} {u u' : Tm}
    (h : WF (L1 ++ (M ++ Entry.defn c u :: L0)))
    (h' : WF (M' ++ Entry.defn c u' :: L0))
    (hiface : SameIface M M')
    (hsealed : ∀ g l r p, Entry.thm g l r p ∈ L1 → c ∉ p.deltaRefs)
    (hfresh : ∀ e ∈ L1, e.name ∉ u'.consts) :
    WF (L1 ++ (M' ++ Entry.defn c u' :: L0)) := by
  induction L1 with
  | nil => simpa using h'
  | cons e L1 ih =>
    have h1 : WF (e :: (L1 ++ (M ++ Entry.defn c u :: L0))) := h
    have hold := h1.fresh_head
    have ih' : WF (L1 ++ (M' ++ Entry.defn c u' :: L0)) :=
      ih h1.tail (fun g l r p hm => hsealed g l r p (List.Mem.tail _ hm))
        (fun e' he' => hfresh e' (List.Mem.tail _ he'))
    have hf : Fresh e.name (L1 ++ (M' ++ Entry.defn c u' :: L0)) := by
      have hM : Fresh e.name M :=
        fun x hx => hold x (List.mem_append_right _ (List.mem_append_left _ hx))
      have hM' := hiface.fresh hM
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hold x (List.mem_append_left _ hx)
      · rcases mem_mid.mp hx with hx | hx
        · rw [hx]
          have hc := hold (Entry.defn c u)
            (List.mem_append_right _ (mem_mid.mpr (Or.inl rfl)))
          exact ⟨hc.1, hfresh e (List.Mem.head _)⟩
        · rcases List.mem_append.mp hx with hx | hx
          · exact hM' x hx
          · exact hold x (List.mem_append_right _ (mem_mid.mpr (Or.inr
              (List.mem_append_right _ hx))))
    show WF (e :: (L1 ++ (M' ++ Entry.defn c u' :: L0)))
    cases h1 with
    | defn _ _ hcl hcu => exact WF.defn ih' hf hcl hcu
    | axm _ _ => exact WF.axm ih' hf
    | @thm _ g l r q _ _ hchk =>
      refine WF.thm ih' hf (hchk.mono_refs ?_ ?_ ?_)
      · intro d v hd hm
        rcases List.mem_append.mp hm with hm | hm
        · exact List.mem_append_left _ hm
        · rcases mem_mid.mp hm with hm | hm
          · cases hm
            exact absurd hd (hsealed g l r q (List.Mem.head _))
          · rcases List.mem_append.mp hm with hm | hm
            · exact List.mem_append_right _ (List.mem_append_left _ (hiface.defn_mem hm))
            · exact List.mem_append_right _ (mem_mid.mpr (Or.inr
                (List.mem_append_right _ hm)))
      · intro a l2 r2 _ hm
        rcases List.mem_append.mp hm with hm | hm
        · exact List.mem_append_left _ hm
        · rcases mem_mid.mp hm with hm | hm
          · cases hm
          · rcases List.mem_append.mp hm with hm | hm
            · exact List.mem_append_right _ (List.mem_append_left _ (hiface.axm_mem hm))
            · exact List.mem_append_right _ (mem_mid.mpr (Or.inr
                (List.mem_append_right _ hm)))
      · intro g' l2 r2 q2 _ hm
        rcases List.mem_append.mp hm with hm | hm
        · exact ⟨q2, List.mem_append_left _ hm⟩
        · rcases mem_mid.mp hm with hm | hm
          · cases hm
          · rcases List.mem_append.mp hm with hm | hm
            · obtain ⟨q', hq'⟩ := hiface.thm_mem hm
              exact ⟨q', List.mem_append_right _ (List.mem_append_left _ hq')⟩
            · exact ⟨q2, List.mem_append_right _ (mem_mid.mpr (Or.inr
                (List.mem_append_right _ hm)))⟩

/-- The variant of Theorem 4.3 without a definition: the proofs of theorems can always be
replaced. -/
theorem replace_proofs {L1 M M' L0 : Lib}
    (h : WF (L1 ++ (M ++ L0))) (h' : WF (M' ++ L0)) (hiface : SameIface M M') :
    WF (L1 ++ (M' ++ L0)) := by
  induction L1 with
  | nil => simpa using h'
  | cons e L1 ih =>
    have h1 : WF (e :: (L1 ++ (M ++ L0))) := h
    have hold := h1.fresh_head
    have ih' : WF (L1 ++ (M' ++ L0)) := ih h1.tail
    have hf : Fresh e.name (L1 ++ (M' ++ L0)) := by
      have hM : Fresh e.name M :=
        fun x hx => hold x (List.mem_append_right _ (List.mem_append_left _ hx))
      have hM' := hiface.fresh hM
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hold x (List.mem_append_left _ hx)
      · rcases List.mem_append.mp hx with hx | hx
        · exact hM' x hx
        · exact hold x (List.mem_append_right _ (List.mem_append_right _ hx))
    show WF (e :: (L1 ++ (M' ++ L0)))
    cases h1 with
    | defn _ _ hcl hcu => exact WF.defn ih' hf hcl hcu
    | axm _ _ => exact WF.axm ih' hf
    | @thm _ g l r q _ _ hchk =>
      refine WF.thm ih' hf (hchk.mono_refs ?_ ?_ ?_)
      · intro d v _ hm
        rcases List.mem_append.mp hm with hm | hm
        · exact List.mem_append_left _ hm
        · rcases List.mem_append.mp hm with hm | hm
          · exact List.mem_append_right _ (List.mem_append_left _ (hiface.defn_mem hm))
          · exact List.mem_append_right _ (List.mem_append_right _ hm)
      · intro a l2 r2 _ hm
        rcases List.mem_append.mp hm with hm | hm
        · exact List.mem_append_left _ hm
        · rcases List.mem_append.mp hm with hm | hm
          · exact List.mem_append_right _ (List.mem_append_left _ (hiface.axm_mem hm))
          · exact List.mem_append_right _ (List.mem_append_right _ hm)
      · intro g' l2 r2 q2 _ hm
        rcases List.mem_append.mp hm with hm | hm
        · exact ⟨q2, List.mem_append_left _ hm⟩
        · rcases List.mem_append.mp hm with hm | hm
          · obtain ⟨q', hq'⟩ := hiface.thm_mem hm
            exact ⟨q', List.mem_append_right _ (List.mem_append_left _ hq')⟩
          · exact ⟨q2, List.mem_append_right _ (List.mem_append_right _ hm)⟩

/-! ## An executable checker (Section 2) -/

def findDef (c : Name) : Lib → Option Tm
  | [] => none
  | Entry.defn d u :: L => if d = c then some u else findDef c L
  | Entry.axm _ _ _ :: L => findDef c L
  | Entry.thm _ _ _ _ :: L => findDef c L

def findAx (a : Name) : Lib → Option (Tm × Tm)
  | [] => none
  | Entry.defn _ _ :: L => findAx a L
  | Entry.axm b l r :: L => if b = a then some (l, r) else findAx a L
  | Entry.thm _ _ _ _ :: L => findAx a L

def findThm (h : Name) : Lib → Option (Tm × Tm)
  | [] => none
  | Entry.defn _ _ :: L => findThm h L
  | Entry.axm _ _ _ :: L => findThm h L
  | Entry.thm g l r _ :: L => if g = h then some (l, r) else findThm h L

/-- The kernel: the equation that a proof establishes, if any. -/
def infer (L : Lib) : Pf → Option (Tm × Tm)
  | .refl t => some (t, t)
  | .symm p =>
    match infer L p with
    | some (l, r) => some (r, l)
    | none => none
  | .trans p q =>
    match infer L p, infer L q with
    | some (l, m), some (m', r) => if m = m' then some (l, r) else none
    | _, _ => none
  | .app p q =>
    match infer L p, infer L q with
    | some (f, f'), some (a, a') => some (.app f a, .app f' a')
    | _, _ => none
  | .lam p =>
    match infer L p with
    | some (b, b') => some (.lam b, .lam b')
    | none => none
  | .beta b a => some (.app (.lam b) a, Tm.inst b a)
  | .delta c =>
    match findDef c L with
    | some u => some (.const c, u)
    | none => none
  | .ax a => findAx a L
  | .lem h => findThm h L

theorem findDef_mem {c : Name} {u : Tm} : ∀ {L : Lib}, findDef c L = some u → Entry.defn c u ∈ L
  | [], h => by simp [findDef] at h
  | Entry.defn d v :: L, h => by
      by_cases e : d = c
      · simp [findDef, e] at h
        rw [e, h]; exact List.Mem.head _
      · simp [findDef, e] at h
        exact List.Mem.tail _ (findDef_mem h)
  | Entry.axm _ _ _ :: L, h => List.Mem.tail _ (findDef_mem (by simpa [findDef] using h))
  | Entry.thm _ _ _ _ :: L, h => List.Mem.tail _ (findDef_mem (by simpa [findDef] using h))

theorem findAx_mem {a : Name} {l r : Tm} :
    ∀ {L : Lib}, findAx a L = some (l, r) → Entry.axm a l r ∈ L
  | [], h => by simp [findAx] at h
  | Entry.defn _ _ :: L, h => List.Mem.tail _ (findAx_mem (by simpa [findAx] using h))
  | Entry.axm b l' r' :: L, h => by
      by_cases e : b = a
      · simp [findAx, e] at h
        rw [e, h.1, h.2]; exact List.Mem.head _
      · simp [findAx, e] at h
        exact List.Mem.tail _ (findAx_mem h)
  | Entry.thm _ _ _ _ :: L, h => List.Mem.tail _ (findAx_mem (by simpa [findAx] using h))

theorem findThm_mem {g : Name} {l r : Tm} :
    ∀ {L : Lib}, findThm g L = some (l, r) → ∃ q, Entry.thm g l r q ∈ L
  | [], h => by simp [findThm] at h
  | Entry.defn _ _ :: L, h => by
      obtain ⟨q, hq⟩ := findThm_mem (L := L) (by simpa [findThm] using h)
      exact ⟨q, List.Mem.tail _ hq⟩
  | Entry.axm _ _ _ :: L, h => by
      obtain ⟨q, hq⟩ := findThm_mem (L := L) (by simpa [findThm] using h)
      exact ⟨q, List.Mem.tail _ hq⟩
  | Entry.thm g' l' r' p :: L, h => by
      by_cases e : g' = g
      · simp [findThm, e] at h
        exact ⟨p, by rw [e, h.1, h.2]; exact List.Mem.head _⟩
      · simp [findThm, e] at h
        obtain ⟨q, hq⟩ := findThm_mem (L := L) h
        exact ⟨q, List.Mem.tail _ hq⟩

/-- Proposition 2.2, first half: the kernel is sound for the checking relation. -/
theorem infer_sound (L : Lib) : ∀ (p : Pf) (l r : Tm), infer L p = some (l, r) → Chk L p l r := by
  intro p
  induction p with
  | refl t =>
    intro l r h
    simp [infer] at h
    rw [← h.1, ← h.2]; exact Chk.refl t
  | symm p ih =>
    intro l r h
    cases hp : infer L p with
    | none => simp [infer, hp] at h
    | some x =>
      obtain ⟨l1, r1⟩ := x
      simp [infer, hp] at h
      rw [← h.1, ← h.2]; exact Chk.symm (ih _ _ hp)
  | trans p q ihp ihq =>
    intro l r h
    cases hp : infer L p with
    | none => simp [infer, hp] at h
    | some x =>
      cases hq : infer L q with
      | none => simp [infer, hp, hq] at h
      | some y =>
        obtain ⟨l1, m⟩ := x
        obtain ⟨m', r1⟩ := y
        by_cases hm : m = m'
        · simp [infer, hp, hq, hm] at h
          rw [← h.1, ← h.2]
          exact Chk.trans (ihp _ _ hp) (hm ▸ ihq _ _ hq)
        · simp [infer, hp, hq, hm] at h
  | app p q ihp ihq =>
    intro l r h
    cases hp : infer L p with
    | none => simp [infer, hp] at h
    | some x =>
      cases hq : infer L q with
      | none => simp [infer, hp, hq] at h
      | some y =>
        obtain ⟨f, f'⟩ := x
        obtain ⟨a, a'⟩ := y
        simp [infer, hp, hq] at h
        rw [← h.1, ← h.2]
        exact Chk.app (ihp _ _ hp) (ihq _ _ hq)
  | lam p ih =>
    intro l r h
    cases hp : infer L p with
    | none => simp [infer, hp] at h
    | some x =>
      obtain ⟨b, b'⟩ := x
      simp [infer, hp] at h
      rw [← h.1, ← h.2]; exact Chk.lam (ih _ _ hp)
  | beta b a =>
    intro l r h
    simp [infer] at h
    rw [← h.1, ← h.2]; exact Chk.beta b a
  | delta c =>
    intro l r h
    cases hd : findDef c L with
    | none => simp [infer, hd] at h
    | some u =>
      simp [infer, hd] at h
      rw [← h.1, ← h.2]; exact Chk.delta (findDef_mem hd)
  | ax a =>
    intro l r h
    exact Chk.ax (findAx_mem (by simpa [infer] using h))
  | lem g =>
    intro l r h
    obtain ⟨q, hq⟩ := findThm_mem (L := L) (by simpa [infer] using h)
    exact Chk.lem hq

def freshb (n : Name) (L : Lib) : Bool :=
  L.all (fun e => decide (e.name ≠ n) && !e.consts.contains n)

theorem freshb_sound {n : Name} {L : Lib} (h : freshb n L = true) : Fresh n L := by
  intro e he
  have h1 := List.all_eq_true.mp h e he
  have h2 : decide (e.name ≠ n) = true ∧ (!e.consts.contains n) = true := by
    simpa [Bool.and_eq_true] using h1
  refine ⟨of_decide_eq_true h2.1, ?_⟩
  intro hm
  have := contains_of_mem hm
  rw [this] at h2
  exact absurd h2.2 (by decide)

/-- A decision procedure for well-formedness. -/
def wfb : Lib → Bool
  | [] => true
  | Entry.defn c u :: L => wfb L && freshb c L && u.closedAt 0 && !u.consts.contains c
  | Entry.axm a _ _ :: L => wfb L && freshb a L
  | Entry.thm h l r p :: L => wfb L && freshb h L && decide (infer L p = some (l, r))

/-- Proposition 2.2, second half: a library that the decision procedure accepts is well
formed. -/
theorem wfb_sound : ∀ (L : Lib), wfb L = true → WF L
  | [], _ => WF.nil
  | Entry.defn c u :: L, h => by
      simp only [wfb, Bool.and_eq_true] at h
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
      refine WF.defn (wfb_sound L h1) (freshb_sound h2) h3 ?_
      intro hm
      rw [contains_of_mem hm] at h4
      exact absurd h4 (by decide)
  | Entry.axm a l r :: L, h => by
      simp only [wfb, Bool.and_eq_true] at h
      exact WF.axm (wfb_sound L h.1) (freshb_sound h.2)
  | Entry.thm g l r p :: L, h => by
      simp only [wfb, Bool.and_eq_true] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      exact WF.thm (wfb_sound L h1) (freshb_sound h2) (infer_sound L p l r (of_decide_eq_true h3))

/-! ## An untrusted prover (Section 2)

Nothing is proved about this prover. Its proofs are accepted only when the kernel checks them. -/

/-- One leftmost-outermost βδ-step, with the proof that justifies it. -/
def step (L : Lib) : Tm → Option (Tm × Pf)
  | .bvar _ => none
  | .const c =>
    match findDef c L with
    | some u => some (u, .delta c)
    | none => none
  | .lam b =>
    match step L b with
    | some (b', p) => some (.lam b', .lam p)
    | none => none
  | .app f a =>
    match f with
    | .lam b => some (Tm.inst b a, .beta b a)
    | _ =>
      match step L f with
      | some (f', p) => some (.app f' a, .app p (.refl a))
      | none =>
        match step L a with
        | some (a', q) => some (.app f a', .app (.refl f) q)
        | none => none

/-- Normalize with the given fuel, returning the result and a proof of the reduction. -/
def norm (L : Lib) : Nat → Tm → Tm × Pf
  | 0, t => (t, .refl t)
  | n + 1, t =>
    match step L t with
    | none => (t, .refl t)
    | some (t', p) => ((norm L n t').1, .trans p (norm L n t').2)

/-- Prove `l ≐ r` by normalizing both sides. -/
def joinPf (L : Lib) (fuel : Nat) (l r : Tm) : Pf :=
  .trans (norm L fuel l).2 (.symm (norm L fuel r).2)

/-! ## The running example (Section 2) -/

namespace Example
open Tm

abbrev nAdd : Name := 0
abbrev nFlip : Name := 1
abbrev nAddComm : Name := 2
abbrev nDouble : Name := 3
abbrev nComp : Name := 4
abbrev nCompDouble : Name := 5
abbrev nQuad : Name := 6
abbrev nQuadComp : Name := 7
abbrev nQuadEq : Name := 8
abbrev nAddFlip : Name := 9
abbrev nDoubleSum : Name := 10

/-- `add s t`, where `add` is a constant without a definition -/
def add2 (s t : Tm) : Tm := app (app (const nAdd) s) t

/-- `flip := λf. λx. λy. f y x` -/
def flipBody : Tm := lam (lam (lam (app (app (bvar 2) (bvar 0)) (bvar 1))))
/-- `double := λx. add x x` -/
def doubleBody : Tm := lam (add2 (bvar 0) (bvar 0))
/-- `comp := λf. λg. λx. f (g x)` -/
def compBody : Tm := lam (lam (lam (app (bvar 2) (app (bvar 1) (bvar 0)))))
/-- `quad := λx. double (double x)` -/
def quadBody : Tm := lam (app (const nDouble) (app (const nDouble) (bvar 0)))
/-- `λx. add (add x x) (add x x)` -/
def four : Tm := lam (add2 (add2 (bvar 0) (bvar 0)) (add2 (bvar 0) (bvar 0)))
/-- `comp double double` -/
def cdd : Tm := app (app (const nComp) (const nDouble)) (const nDouble)
/-- `λx. λy. add y x` -/
def swapped : Tm := lam (lam (add2 (bvar 0) (bvar 1)))
/-- `λx. λy. double (add x y)` -/
def doubleSumL : Tm := lam (lam (app (const nDouble) (add2 (bvar 1) (bvar 0))))
/-- `λx. λy. add (add y x) (add x y)` -/
def doubleSumR : Tm := lam (lam (add2 (add2 (bvar 0) (bvar 1)) (add2 (bvar 1) (bvar 0))))
/-- `λx. λy. add ((λa. λb. add b a) x y) (add x y)`, the middle term of the proof below -/
def doubleSumM : Tm :=
  lam (lam (add2 (app (app swapped (bvar 1)) (bvar 0)) (add2 (bvar 1) (bvar 0))))
/-- `flip add` -/
def flipAdd : Tm := app (const nFlip) (const nAdd)

/-! The library, built oldest entry first. -/

def L1 : Lib := [Entry.defn nFlip flipBody]
def L2 : Lib := Entry.axm nAddComm flipAdd (const nAdd) :: L1
def L3 : Lib := Entry.defn nDouble doubleBody :: L2
def L4 : Lib := Entry.defn nComp compBody :: L3
def pCompDouble : Pf := joinPf L4 32 cdd four
def L5 : Lib := Entry.thm nCompDouble cdd four pCompDouble :: L4
def L6 : Lib := Entry.defn nQuad quadBody :: L5
def pQuadComp : Pf := joinPf L6 32 (const nQuad) cdd
def L7 : Lib := Entry.thm nQuadComp (const nQuad) cdd pQuadComp :: L6
def pQuadEq : Pf := Pf.trans (Pf.lem nQuadComp) (Pf.lem nCompDouble)
def L8 : Lib := Entry.thm nQuadEq (const nQuad) four pQuadEq :: L7
def pAddFlip : Pf := Pf.trans (Pf.symm (Pf.ax nAddComm)) (norm L8 32 flipAdd).2
def L9 : Lib := Entry.thm nAddFlip (const nAdd) swapped pAddFlip :: L8
/-- Normalize the left side, rewrite one occurrence of `add` with `add_flip`, normalize. -/
def pDoubleSum : Pf :=
  Pf.trans (norm L9 32 doubleSumL).2
    (Pf.trans
      (Pf.lam (Pf.lam (Pf.app
        (Pf.app (Pf.refl (const nAdd))
          (Pf.app (Pf.app (Pf.lem nAddFlip) (Pf.refl (bvar 1))) (Pf.refl (bvar 0))))
        (Pf.refl (add2 (bvar 1) (bvar 0))))))
      (norm L9 32 doubleSumM).2)
def L10 : Lib := Entry.thm nDoubleSum doubleSumL doubleSumR pDoubleSum :: L9

/-- The example library is well formed: the kernel accepts every proof in it. -/
theorem L10_wf : WF L10 := wfb_sound L10 (by decide)

/-- `comp_double` is checked against `L4`. Its audit surface is `comp` and `double`. -/
example : (auditLib L4 pCompDouble cdd four).map Entry.name = [nComp, nDouble] := by
  decide

/-- `quad_comp` is checked against `L6`. Its audit surface is `quad`, `comp`, and `double`. -/
example : (auditLib L6 pQuadComp (const nQuad) cdd).map Entry.name = [nQuad, nComp, nDouble] := by
  decide

/-- `add_flip` is checked against `L8`. Its statement mentions only `add`, and its audit
surface is the axiom `add_comm` with the definition `flip` in that axiom. -/
example : (auditLib L8 pAddFlip (const nAdd) swapped).map Entry.name = [nAddComm, nFlip] := by
  decide

/-- `quad_eq` is checked against `L7`. Its audit surface is `quad` and `double`. -/
example : (auditLib L7 pQuadEq (const nQuad) four).map Entry.name = [nQuad, nDouble] := by
  decide

/-- The proof over the audit surface is accepted by the kernel, as Theorem 3.4 says. -/
example : infer (auditLib L7 pQuadEq (const nQuad) four) (auditPf L7 pQuadEq (const nQuad) four)
    = some (const nQuad, four) := by
  decide

/-- `double_sum` is checked against `L9`. Its statement mentions `double` and `add`, and its
audit surface also holds the axiom `add_comm` and the definition `flip` in that axiom. -/
example : (auditLib L9 pDoubleSum doubleSumL doubleSumR).map Entry.name
    = [nDouble, nAddComm, nFlip] := by
  decide

example : infer (auditLib L9 pDoubleSum doubleSumL doubleSumR)
    (auditPf L9 pDoubleSum doubleSumL doubleSumR) = some (doubleSumL, doubleSumR) := by
  decide

/-- The kernel rejects the proof of `double_sum` that only normalizes both sides and uses no
axiom. -/
example : infer L9 (joinPf L9 32 doubleSumL doubleSumR) = none := by
  decide

end Example

end Audit

/-! The axioms the main results depend on. -/
#print axioms Audit.Chk.mono_refs
#print axioms Audit.infer_sound
#print axioms Audit.wfb_sound
#print axioms Audit.close_closed
#print axioms Audit.close_least
#print axioms Audit.axRefs_unfoldLems_sub
#print axioms Audit.audit_sound_usedAx
#print axioms Audit.restrict_wf
#print axioms Audit.audit_surface
#print axioms Audit.portable
#print axioms Audit.merge
#print axioms Audit.replace
#print axioms Audit.replace_proofs
#print axioms Audit.Example.L10_wf
