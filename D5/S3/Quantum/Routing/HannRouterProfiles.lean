/- GID: D5/S3/Quantum/Routing/HannRouterProfiles
   generality: G
   mirror-B: D5/B/S3/Quantum/Routing/HannRouterProfiles
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal internal router localization and active-profile separation. -/

import D5.S3.Quantum.Routing.HannSpatialQram

/-! Observations of loaded internal routers and their active address profiles. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Routing.HannRouterProfiles

open HannSpatialQram
open ReversibleQram (Address)

/-- Exactly the internal routers: a root or a router in one of its two children. -/
abbrev Router : ℕ → Type
  | 0 => Empty
  | n + 1 => Option (Bool × Router n)

/-- Read the literal router field, never an incident or output rail. -/
def routerLabel : (n : ℕ) → Tree n → Router n → Qutrit
  | 0, _, v => nomatch v
  | _ + 1, t, none => t.2.1
  | n + 1, t, some (b, v) => routerLabel n (if b then t.2.2.2 else t.2.2.1) v

/-- Append the final bit while preserving the circuit's head-first address order. -/
def snoc : (n : ℕ) → Address n → Bool → Address (n + 1)
  | 0, _, b => (b, ())
  | n + 1, a, b => (a.1, snoc n a.2 b)

/-- The depth-n router reached by a length-n prefix in a tree of depth n+1. -/
def deepest : (n : ℕ) → Address n → Router (n + 1)
  | 0, _ => none
  | n + 1, a => some (a.1, deepest n a.2)

/-- Router labels after the actual sequential load, with any external qutrit bus. -/
def loadedLabel (n : ℕ) (a : Address n) (bus : Qutrit) (v : Router n) : Qutrit :=
  routerLabel n ((load n n) (loading n a bus 0)).2.2 v

private theorem loaded_label (n : ℕ) (a : Address n) (bus : Qutrit) (v : Router n) :
    loadedLabel n a bus v = routerLabel n (programmed n a n) v := by
  unfold loadedLabel
  rw [correctness.1 n a bus n (le_refl n)]
  rfl

private theorem vacuum_label (n : ℕ) (v : Router n) :
    routerLabel n (vacuum n) v = Qutrit.wait := by
  induction n with
  | zero => exact v.elim
  | succ n ih =>
      cases v with
      | none => rfl
      | some v => rcases v with ⟨b, v⟩; cases b <;> exact ih v

private theorem deepest_label (n : ℕ) (u i : Address n) (b : Bool) :
    routerLabel (n + 1) (programmed (n + 1) (snoc n u b) (n + 1)) (deepest n i) =
      if i = u then encode b else Qutrit.wait := by
  induction n with
  | zero => cases u; cases i; simp [routerLabel, programmed, snoc, deepest]
  | succ n ih =>
      rcases u with ⟨c, u⟩
      rcases i with ⟨d, i⟩
      cases c <;> cases d
      · change routerLabel (n + 1) (programmed (n + 1) (snoc n u b) (n + 1))
          (deepest n i) = if (false, i) = (false, u) then encode b else Qutrit.wait
        simpa only [Prod.mk.injEq, eq_self, true_and] using ih u i
      · simp [snoc, deepest, programmed, routerLabel, vacuum_label]
      · simp [snoc, deepest, programmed, routerLabel, vacuum_label]
      · change routerLabel (n + 1) (programmed (n + 1) (snoc n u b) (n + 1))
          (deepest n i) = if (true, i) = (true, u) then encode b else Qutrit.wait
        simpa only [Prod.mk.injEq, eq_self, true_and] using ih u i

private theorem sibling_labels (n : ℕ) (u : Address n) (v : Router (n + 1))
    (hv : v ≠ deepest n u) :
    routerLabel (n + 1) (programmed (n + 1) (snoc n u false) (n + 1)) v =
      routerLabel (n + 1) (programmed (n + 1) (snoc n u true) (n + 1)) v := by
  induction n with
  | zero => cases v with
      | none => exact (hv rfl).elim
      | some v => exact v.2.elim
  | succ n ih =>
      rcases u with ⟨b, u⟩
      cases v with
      | none => rfl
      | some v =>
          rcases v with ⟨c, v⟩
          cases b <;> cases c
          · change routerLabel (n + 1) (programmed (n + 1) (snoc n u false) (n + 1)) v =
              routerLabel (n + 1) (programmed (n + 1) (snoc n u true) (n + 1)) v
            exact ih u v (by simpa [deepest] using hv)
          · simp [snoc, routerLabel, programmed]
          · simp [snoc, routerLabel, programmed]
          · change routerLabel (n + 1) (programmed (n + 1) (snoc n u false) (n + 1)) v =
              routerLabel (n + 1) (programmed (n + 1) (snoc n u true) (n + 1)) v
            exact ih u v (by simpa [deepest] using hv)

private theorem snoc_surjective (n : ℕ) (a : Address (n + 1)) :
    ∃ u b, a = snoc n u b := by
  induction n with
  | zero => exact ⟨(), a.1, by cases a with | mk b a => cases a; rfl⟩
  | succ n ih =>
      obtain ⟨u, b, h⟩ := ih a.2
      exact ⟨(a.1, u), b, by cases a; simp_all [snoc]⟩

private theorem snoc_ne (n : ℕ) (u : Address n) : snoc n u false ≠ snoc n u true := by
  induction n with
  | zero => simp [snoc]
  | succ n ih => simpa [snoc] using ih u.2

private theorem encode_injective : Function.Injective encode := by
  intro b c h
  cases b <;> cases c <;> simp_all [encode]

private theorem encode_ne_wait (b : Bool) : encode b ≠ Qutrit.wait := by
  cases b <;> simp [encode]

/-- Two addresses have the same active profile exactly when all observable loaded routers agree.
The two buses may differ; no bus coordinate is observed. -/
def SameProfile (n : ℕ) (q : Router n → ℝ) (a a' : Address n)
    (bus bus' : Qutrit) : Prop :=
  ∀ v, q v < 1 → loadedLabel n a bus v = loadedLabel n a' bus' v

/-- The active physical router profile distinguishes every address. -/
def Separates (n : ℕ) (q : Router n → ℝ) : Prop :=
  ∀ a a' bus bus', SameProfile n q a a' bus bus' → a = a'

/-- Exact all-depth physical separation criterion, including arbitrary independent endpoint rates.
No interval restriction is needed for the stronger combinatorial statement. -/
theorem profile_separation_iff (n : ℕ) (q : Router (n + 1) → ℝ) :
    (∀ (a a' : Address (n + 1)) (bus bus' : Qutrit),
      (∀ v, q v < 1 → loadedLabel (n + 1) a bus v = loadedLabel (n + 1) a' bus' v) →
        a = a') ↔ ∀ u : Address n, q (deepest n u) < 1 := by
  change Separates (n + 1) q ↔ _
  constructor
  · intro h u
    by_contra hq
    apply snoc_ne n u
    apply h (snoc n u false) (snoc n u true) Qutrit.wait Qutrit.wait
    intro v hv
    rw [loaded_label, loaded_label]
    apply sibling_labels
    intro heq
    exact hq (heq ▸ hv)
  · intro hq a a' bus bus' h
    obtain ⟨u, b, rfl⟩ := snoc_surjective n a
    obtain ⟨u', b', rfl⟩ := snoc_surjective n a'
    have he := h (deepest n u) (hq u)
    rw [loaded_label, loaded_label, deepest_label, deepest_label] at he
    have huu : u = u' := by
      by_contra hu
      simp only [ite_true, ite_eq_right hu] at he
      exact encode_ne_wait b he
    subst u'
    simp only [ite_true] at he
    have hb : b = b' := encode_injective he
    subst b'
    rfl

#print axioms profile_separation_iff

end D5.S3.Quantum.Routing.HannRouterProfiles
