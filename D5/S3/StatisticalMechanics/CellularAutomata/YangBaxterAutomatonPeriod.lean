/- GID: D5/S3/StatisticalMechanics/CellularAutomata/YangBaxterAutomatonPeriod
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/CellularAutomata/YangBaxterAutomatonPeriod
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The Yang-Baxter automata over F_{2^n} have period dividing 2^n (arXiv:2602.17148). -/

/-
proof_shape: isPGroup_closure_of_commuting_involutions: content; isPGroup_cycle: content;
  exists_translation: content; step_iterate_card: content; result: content
escape_witness: form (1): the private proposition `exists_translation` (a bijective solution `f`
  of (FYB) on a nontrivial finite group of exponent 2 has `u ≠ 0` with `f (x + u) = f x + u`),
  proved from `isPGroup_cycle` and used by `step_iterate_card` on the live path of `result`
admission_basis: open-problem-resolution (issue #11405)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.CellularAutomata.YangBaxterAutomatonPeriod

/-!
A. Araoka and T. Tokihiro, *Integrable cellular automata on finite fields of order 2^n*,
arXiv:2602.17148 (Math. Phys. Anal. Geom. 29, 30 (2026)). For a map `f` of a finite field of
characteristic 2, the R-matrix `R(x, y) = (y + f(x + y), x - f(x + y))` solves the Yang–Baxter
equation exactly when `f x + f (x + f y) = f (x + f (y + f x))` (FYB). The automaton runs `R` along
a row of `N` cells, `R(x_i, y_{i-1}) = (x_i', y_i)` with `y_0 = b`, and the helical boundary
condition feeds `y_N` back as the next boundary value. The paper conjectures that for bijective
`f` the period divides the order `q` of the field, and proves it for `q = 4, 8`. It holds for
every `q`: normalising `f(0) = 0`, the involutions `L_x = t_x f t_x` satisfy the cycle identity and
generate a 2-group, which together with the translations `t_a` generates a 2-group; a nontrivial
central element is a translation `t_u` commuting with `f`, so `f (x + u) = f x + u`. The automaton
then descends to `F/⟨u⟩`, commutes with adding `{0, u}`-valued states, and induction on `q` gives
`step^q = id`.
-/

open Equiv

section Automaton

variable {V : Type*} [AddCommGroup V]

/-- The R-matrix `(x, y) ↦ (y + f(x + y), x - f(x + y))`. -/
def rmat (f : V → V) (x y : V) : V × V := (y + f (x + y), x - f (x + y))

/-- The auxiliary values: `carry 0 = b`, and `carry (i + 1)` is the second output of `R` at cell
`i`. -/
def carry (f : V → V) {N : ℕ} (x : Fin N → V) (b : V) : ℕ → V
  | 0 => b
  | i + 1 => if h : i < N then (rmat f (x ⟨i, h⟩) (carry f x b i)).2 else carry f x b i

/-- One time step of the cellular automaton with the helical boundary condition: the new cell
values and the new boundary value. -/
def step (f : V → V) {N : ℕ} (s : (Fin N → V) × V) : (Fin N → V) × V :=
  (fun i => (rmat f (s.1 i) (carry f s.1 s.2 i)).1, carry f s.1 s.2 N)

end Automaton

/-- The conjecture of arXiv:2602.17148: over a finite field of characteristic 2, the automaton built
from a bijective solution of (FYB) has period dividing the order of the field. -/
def claim : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [CharP F 2] (f : F → F), f.Bijective →
    (∀ x y, f x + f (x + f y) = f (x + f (y + f x))) →
    ∀ N : ℕ, (step f (N := N))^[Fintype.card F] = id

/-- Pairwise commuting involutions generate a 2-group. -/
private theorem isPGroup_closure_of_commuting_involutions {G : Type*} [Group G] (S : Set G)
    (hSc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hSi : ∀ x ∈ S, x * x = 1) :
    IsPGroup 2 (Subgroup.closure S) := by
  have hc : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val
      ((Subgroup.isMulCommutative_closure hSc).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hsq : ∀ x ∈ Subgroup.closure S, x * x = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hSi x hx
    | one => simp
    | mul x y hx hy ihx ihy =>
      calc x * y * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
        _ = x * (x * y) * y := by rw [hc y hy x hx]
        _ = 1 := by rw [← mul_assoc, ihx, one_mul, ihy]
    | inv x hx ihx =>
      rw [← mul_inv_rev, ihx, inv_one]
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  simp [pow_two, hsq g.1 g.2]

/-- Involutions `L x` fixing `x` and satisfying the cycle identity generate a 2-group. -/
private theorem isPGroup_cycle {X : Type*} [Finite X] (L : X → Perm X)
    (hfix : ∀ x, L x x = x) (hinv : ∀ x, L x * L x = 1)
    (hcyc : ∀ x y, L (L x y) * L x = L (L y x) * L y) :
    IsPGroup 2 (Subgroup.closure (Set.range L)) := by
  set P := Subgroup.closure (Set.range L)
  have hL : ∀ x, L x ∈ P := fun x => Subgroup.subset_closure ⟨x, rfl⟩
  have hi : ∀ z, (L z)⁻¹ = L z := fun z => inv_eq_of_mul_eq_one_right (hinv z)
  have hcyc' : ∀ x y, L x * L (L x y) = L y * L (L y x) := by
    intro x y
    have h := congrArg (·⁻¹) (hcyc x y)
    simpa only [mul_inv_rev, hi] using h
  have hback : ∀ (p : Perm X) (z : X), (p * L (p⁻¹ z))⁻¹ z = p⁻¹ z := by
    intro p z
    rw [mul_inv_rev, hi, Perm.mul_apply, hfix]
  let φ : X → P → P := fun z p => ⟨p * L ((p : Perm X)⁻¹ z), P.mul_mem p.2 (hL _)⟩
  have hφinv : ∀ z, Function.Involutive (φ z) := by
    intro z p
    apply Subtype.ext
    change (p : Perm X) * L ((p : Perm X)⁻¹ z) * L (((p : Perm X) * L ((p : Perm X)⁻¹ z))⁻¹ z) = p
    rw [hback, mul_assoc, hinv, mul_one]
  let Φ : X → Perm P := fun z => (hφinv z).toPerm
  have hΦ : ∀ z p, Φ z p = φ z p := fun _ _ => rfl
  have hcomm : ∀ x y, Φ x * Φ y = Φ y * Φ x := by
    intro x y
    refine Equiv.ext fun p => Subtype.ext ?_
    simp only [Perm.mul_apply, hΦ]
    change (p : Perm X) * L ((p : Perm X)⁻¹ y) * L (((p : Perm X) * L ((p : Perm X)⁻¹ y))⁻¹ x) =
      (p : Perm X) * L ((p : Perm X)⁻¹ x) * L (((p : Perm X) * L ((p : Perm X)⁻¹ x))⁻¹ y)
    rw [mul_inv_rev, hi, Perm.mul_apply, mul_inv_rev, hi, Perm.mul_apply, mul_assoc, mul_assoc,
      hcyc']
  have hΦ2 : ∀ x, Φ x * Φ x = 1 := by
    intro x
    refine Equiv.ext fun p => ?_
    simp only [Perm.mul_apply, Perm.one_apply, hΦ]
    exact hφinv x p
  set E := Subgroup.closure (Set.range Φ)
  have hE : IsPGroup 2 E := by
    refine isPGroup_closure_of_commuting_involutions _ ?_ ?_
    · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩; exact hcomm x y
    · rintro _ ⟨x, rfl⟩; exact hΦ2 x
  have hΦE : ∀ z, Φ z ∈ E := fun z => Subgroup.subset_closure ⟨z, rfl⟩
  have horb : ∀ p : P, p ∈ MulAction.orbit E (1 : P) := by
    rintro ⟨p, hp⟩
    induction hp using Subgroup.closure_induction_right with
    | one => exact MulAction.mem_orbit_self _
    | mul_right x hx y hy ih =>
      obtain ⟨a, rfl⟩ := hy
      obtain ⟨e, he⟩ := ih
      refine ⟨⟨Φ (x a), hΦE _⟩ * e, ?_⟩
      change (⟨Φ (x a), hΦE _⟩ * e) • (1 : P) = _
      change e • (1 : P) = _ at he
      rw [mul_smul, he]
      apply Subtype.ext
      change x * L (x⁻¹ (x a)) = x * L a
      simp
    | mul_inv_cancel x hx y hy ih =>
      obtain ⟨a, rfl⟩ := hy
      obtain ⟨e, he⟩ := ih
      refine ⟨⟨Φ (x a), hΦE _⟩ * e, ?_⟩
      change (⟨Φ (x a), hΦE _⟩ * e) • (1 : P) = _
      change e • (1 : P) = _ at he
      rw [mul_smul, he]
      apply Subtype.ext
      change x * L (x⁻¹ (x a)) = x * (L a)⁻¹
      simp [hi]
  have huniv : MulAction.orbit E (1 : P) = Set.univ := Set.eq_univ_of_forall horb
  obtain ⟨n, hn⟩ := hE.card_orbit (1 : P)
  refine IsPGroup.of_card (n := n) ?_
  rw [← hn, huniv, Nat.card_congr (Equiv.Set.univ P)]

/-- A bijective solution of (FYB) on a nontrivial finite group of exponent 2 commutes with some
nonzero translation. -/
private theorem exists_translation {V : Type*} [AddCommGroup V] [Finite V] [Nontrivial V]
    (h2 : ∀ x : V, x + x = 0) (f : V → V) (hf : f.Bijective)
    (hfyb : ∀ x y, f x + f (x + f y) = f (x + f (y + f x))) :
    ∃ u : V, u ≠ 0 ∧ ∀ x, f (x + u) = f x + u := by
  have normalised : ∀ g : V → V, g.Bijective → g 0 = 0 →
      (∀ x y, g x + g (x + g y) = g (x + g (y + g x))) →
      ∃ u : V, u ≠ 0 ∧ ∀ x, g (x + u) = g x + u := by
    intro g hg hg0 hfyb
    have hc : ∀ x y : V, x + (x + y) = y := fun x y => by rw [← add_assoc, h2, zero_add]
    have hc' : ∀ x y : V, y + x + x = y := fun x y => by rw [add_assoc, h2, add_zero]
    -- `g` is an involution.
    have ginv : ∀ x, g (g x) = x := by
      intro x
      have h := hfyb x 0
      rw [hg0, add_zero, h2, zero_add] at h
      have h' : g (x + g (g x)) = g 0 := by rw [← h, hg0]
      have := hg.1 h'
      calc g (g x) = x + (x + g (g x)) := (hc x _).symm
        _ = x := by rw [this, add_zero]
    -- Identity (I).
    have hI : ∀ c d, g (g c + g (c + d)) = c + g (g c + g d) := by
      intro c d
      have h := hfyb (g c) d
      rw [ginv] at h
      rw [add_comm d c] at h
      exact h.symm
    let gp : Equiv.Perm V := Equiv.ofBijective g hg
    let t : V → Equiv.Perm V := fun a => Equiv.addRight a
    let L : V → Equiv.Perm V := fun x => t x * gp * t x
    have hLapp : ∀ x y, L x y = g (y + x) + x := fun _ _ => rfl
    have hfix : ∀ x, L x x = x := by intro x; rw [hLapp, h2, hg0, zero_add]
    have hinv : ∀ x, L x * L x = 1 := by
      intro x
      refine Equiv.ext fun y => ?_
      rw [Equiv.Perm.mul_apply, hLapp, hLapp, hc', ginv, hc', Equiv.Perm.one_apply]
    have hcyc : ∀ x y, L (L x y) * L x = L (L y x) * L y := by
      intro x y
      refine Equiv.ext fun z => ?_
      simp only [Equiv.Perm.mul_apply, hLapp]
      rw [show g (z + x) + x + (g (y + x) + x) = g (z + x) + g (y + x) + (x + x) by abel, h2,
        add_zero,
        show g (z + y) + y + (g (x + y) + y) = g (z + y) + g (x + y) + (y + y) by abel, h2,
        add_zero, add_comm x y]
      have key := hI (y + x) (z + x)
      rw [show y + x + (z + x) = z + y + (x + x) by abel, h2, add_zero] at key
      rw [add_comm (g (z + y)) (g (y + x)), key, add_comm (g (z + x)) (g (y + x)),
        show y + x + g (g (y + x) + g (z + x)) + (g (y + x) + y) =
          g (g (y + x) + g (z + x)) + (g (y + x) + x) + (y + y) by abel, h2, add_zero]
    set P := Subgroup.closure (Set.range L)
    have hP : IsPGroup 2 P := isPGroup_cycle L hfix hinv hcyc
    have htapp : ∀ a y, t a y = y + a := fun _ _ => rfl
    have ht_mul : ∀ a b, t a * t b = t (a + b) := by
      intro a b
      refine Equiv.ext fun y => ?_
      rw [Equiv.Perm.mul_apply, htapp, htapp, htapp, add_assoc, add_comm b a]
    have ht_sq : ∀ a, t a * t a = 1 := by
      intro a
      refine Equiv.ext fun y => ?_
      rw [ht_mul, h2, htapp, add_zero, Equiv.Perm.one_apply]
    have ht_inv : ∀ a, (t a)⁻¹ = t a := fun a => inv_eq_of_mul_eq_one_right (ht_sq a)
    set T := Subgroup.closure (Set.range t)
    have hT : IsPGroup 2 T := by
      refine isPGroup_closure_of_commuting_involutions _ ?_ ?_
      · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
        rw [ht_mul, ht_mul, add_comm]
      · rintro _ ⟨a, rfl⟩
        exact ht_sq a
    have hconj : ∀ a x, t a * L x * (t a)⁻¹ = L (x + a) := by
      intro a x
      refine Equiv.ext fun y => ?_
      simp only [ht_inv, Equiv.Perm.mul_apply, hLapp, htapp]
      rw [show y + a + x = y + (x + a) by abel, add_assoc]
    have hmap : ∀ a, ∀ h ∈ P, t a * h * (t a)⁻¹ ∈ P := by
      intro a h hh
      induction hh using Subgroup.closure_induction with
      | mem _ hy =>
        obtain ⟨x, rfl⟩ := hy
        rw [hconj]
        exact Subgroup.subset_closure ⟨_, rfl⟩
      | one => simp
      | mul u v _ _ hu hv =>
        have e : t a * (u * v) * (t a)⁻¹ = (t a * u * (t a)⁻¹) * (t a * v * (t a)⁻¹) := by group
        rw [e]
        exact P.mul_mem hu hv
      | inv u _ hu =>
        have e : t a * u⁻¹ * (t a)⁻¹ = (t a * u * (t a)⁻¹)⁻¹ := by group
        rw [e]
        exact P.inv_mem hu
    have hTN : T ≤ Subgroup.normalizer (P : Set (Equiv.Perm V)) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨a, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
      intro h
      refine ⟨hmap a h, fun hh => ?_⟩
      have e := hmap a _ hh
      rwa [ht_inv, show t a * (t a * h * t a) * t a = (t a * t a) * h * (t a * t a) by group, ht_sq,
        one_mul, mul_one] at e
    have hQ : IsPGroup 2 (T ⊔ P : Subgroup (Equiv.Perm V)) :=
      IsPGroup.to_sup_of_normal_right' hT hP hTN
    set Q := T ⊔ P
    have htQ : ∀ a, t a ∈ Q := fun a => (le_sup_left : T ≤ Q) (Subgroup.subset_closure ⟨a, rfl⟩)
    have hLQ : ∀ x, L x ∈ Q := fun x => (le_sup_right : P ≤ Q) (Subgroup.subset_closure ⟨x, rfl⟩)
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have : Nontrivial Q := by
      refine ⟨⟨⟨t v, htQ v⟩, 1, fun h => hv ?_⟩⟩
      have := congrArg (fun q : Q => (q : Equiv.Perm V) 0) h
      simpa [htapp] using this
    have := hQ.center_nontrivial
    obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center Q)
    have hzc : ∀ q : Q, q * z = z * q := Subgroup.mem_center_iff.mp z.2
    set w : Equiv.Perm V := ((z : Q) : Equiv.Perm V) with hw
    have hwt : ∀ a, w a = w 0 + a := by
      intro a
      have e := congrArg (fun q : Q => (q : Equiv.Perm V) 0) (hzc ⟨t a, htQ a⟩)
      simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply] at e
      rw [htapp, htapp, zero_add] at e
      exact e.symm
    refine ⟨w 0, fun h0 => hz ?_, fun x => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      refine Equiv.ext fun a => ?_
      change w a = a
      rw [hwt, h0, zero_add]
    · have e := congrArg (fun q : Q => (q : Equiv.Perm V) x) (hzc ⟨L 0, hLQ 0⟩)
      simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply] at e
      rw [← hw, hLapp, hLapp, add_zero, add_zero, add_zero, add_zero, hwt x, hwt (g x)] at e
      rw [add_comm x, e, add_comm]
  obtain ⟨a, ha⟩ := hf.2 0
  have hg : (fun x => f (x + a)).Bijective := hf.comp (Equiv.addRight a).bijective
  have hgfyb : ∀ x y, f (x + a) + f (x + f (y + a) + a) = f (x + f (y + f (x + a) + a) + a) := by
    intro x y
    have e := hfyb (x + a) (y + a)
    rwa [show x + a + f (y + a) = x + f (y + a) + a by abel,
      show x + a + f (y + a + f (x + a)) = x + f (y + f (x + a) + a) + a by abel_nf] at e
  obtain ⟨u, hu, hgu⟩ := normalised (fun x => f (x + a)) hg
    (by simp only [zero_add, ha]) hgfyb
  refine ⟨u, hu, fun x => ?_⟩
  have e := hgu (x + a)
  rwa [show x + a + u + a = x + u + (a + a) by abel, h2, add_zero,
    show x + a + a = x + (a + a) by abel, h2, add_zero] at e

/-- The automaton over a finite group of exponent 2 has period dividing its order. -/
private theorem step_iterate_card (n : ℕ) : ∀ (V : Type) [AddCommGroup V] [Finite V],
    Nat.card V = n → (∀ x : V, x + x = 0) → ∀ f : V → V, f.Bijective →
    (∀ x y, f x + f (x + f y) = f (x + f (y + f x))) → ∀ N : ℕ, (step f (N := N))^[n] = id := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ hcard h2 f hf hfyb N
  rcases subsingleton_or_nontrivial V with hV | hV
  · have hn : n = 1 := by rw [← hcard]; exact Nat.card_unique
    subst hn
    funext s
    exact Subsingleton.elim _ _
  obtain ⟨u, hu, hfu⟩ := exists_translation h2 f hf hfyb
  set H := AddSubgroup.zmultiples u
  have hu2 : addOrderOf u = 2 := addOrderOf_eq_prime (by rw [two_nsmul, h2]) hu
  have hH : ∀ h ∈ H, h = 0 ∨ h = u := by
    intro h hh
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hh
    rw [← mod_addOrderOf_zsmul, hu2, Nat.cast_ofNat]
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left
      rw [hk, zero_zsmul]
    · right
      rw [hk, one_zsmul]
  have hfH : ∀ h ∈ H, ∀ x, f (x + h) = f x + h := by
    intro h hh x
    rcases hH h hh with rfl | rfl
    · simp
    · exact hfu x
  have step_add : ∀ s δ : (Fin N → V) × V, (∀ i, δ.1 i ∈ H) → δ.2 ∈ H →
      step f (s + δ) = step f s + δ := by
    intro s δ hδ1 hδ2
    have hneg : ∀ x : V, -x = x := fun x => neg_eq_of_add_eq_zero_right (h2 x)
    have hcarry : ∀ i, carry f (s.1 + δ.1) (s.2 + δ.2) i = carry f s.1 s.2 i + δ.2 := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih =>
        simp only [carry]
        split_ifs with h
        · simp only [rmat, Pi.add_apply, ih]
          rw [show s.1 ⟨i, h⟩ + δ.1 ⟨i, h⟩ + (carry f s.1 s.2 i + δ.2) =
            s.1 ⟨i, h⟩ + carry f s.1 s.2 i + (δ.1 ⟨i, h⟩ + δ.2) by abel,
            hfH _ (H.add_mem (hδ1 _) hδ2), sub_eq_add_neg, sub_eq_add_neg, neg_add,
            hneg (δ.1 _ + δ.2),
            hneg]
          rw [show s.1 ⟨i, h⟩ + δ.1 ⟨i, h⟩ + (f (s.1 ⟨i, h⟩ + carry f s.1 s.2 i) +
            (δ.1 ⟨i, h⟩ + δ.2)) = s.1 ⟨i, h⟩ + f (s.1 ⟨i, h⟩ + carry f s.1 s.2 i) + δ.2 +
            (δ.1 ⟨i, h⟩ + δ.1 ⟨i, h⟩) by abel, h2, add_zero]
        · exact ih
    apply Prod.ext
    · funext i
      simp only [step, Prod.fst_add, Prod.snd_add, Pi.add_apply, rmat, hcarry]
      rw [show s.1 i + δ.1 i + (carry f s.1 s.2 i + δ.2) =
          s.1 i + carry f s.1 s.2 i + (δ.1 i + δ.2) by
        abel, hfH _ (H.add_mem (hδ1 _) hδ2)]
      rw [show carry f s.1 s.2 i + δ.2 + (f (s.1 i + carry f s.1 s.2 i) + (δ.1 i + δ.2)) =
        carry f s.1 s.2 i + f (s.1 i + carry f s.1 s.2 i) + δ.1 i + (δ.2 + δ.2) by abel, h2,
        add_zero]
    · simp only [step, Prod.fst_add, Prod.snd_add, hcarry]
  let π : V →+ V ⧸ H := QuotientAddGroup.mk' H
  let f' : V ⧸ H → V ⧸ H := Quotient.map' f (fun a b hab => by
    rw [QuotientAddGroup.leftRel_apply] at hab ⊢
    have e := hfH _ hab a
    rw [add_neg_cancel_left] at e
    rw [e, neg_add_cancel_left]
    exact hab)
  have hπf : ∀ x, f' (π x) = π (f x) := fun _ => rfl
  have step_map : ∀ s : (Fin N → V) × V, step f' ((fun i => π (s.1 i)), π s.2) =
      ((fun i => π ((step f s).1 i)), π (step f s).2) := by
    intro s
    have hcarry : ∀ i, carry f' (fun j => π (s.1 j)) (π s.2) i = π (carry f s.1 s.2 i) := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih =>
        simp only [carry]
        split_ifs with h
        · simp only [rmat, ih, ← map_add, hπf, ← map_sub]
        · exact ih
    apply Prod.ext
    · funext i
      simp only [step, rmat, hcarry, ← map_add, hπf]
    · simp only [step, hcarry]
  have hπ : Function.Surjective π := QuotientAddGroup.mk'_surjective H
  have h2' : ∀ y : V ⧸ H, y + y = 0 := by
    intro y
    obtain ⟨x, rfl⟩ := hπ y
    rw [← map_add, h2, map_zero]
  have hf' : f'.Bijective := by
    have hs : f'.Surjective := by
      intro y
      obtain ⟨x, rfl⟩ := hπ y
      obtain ⟨z, rfl⟩ := hf.2 x
      exact ⟨π z, hπf z⟩
    exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
  have hfyb' : ∀ x y, f' x + f' (x + f' y) = f' (x + f' (y + f' x)) := by
    intro x y
    obtain ⟨a, rfl⟩ := hπ x
    obtain ⟨b, rfl⟩ := hπ y
    simp only [hπf, ← map_add, hfyb]
  have hcardH : Nat.card H = 2 := by rw [Nat.card_zmultiples, hu2]
  have hsplit : Nat.card V = Nat.card (V ⧸ H) * 2 := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H, hcardH]
  set m := Nat.card (V ⧸ H)
  have hm : m < n := by
    have : 0 < m := Nat.card_pos
    omega
  have ihm := ih m hm (V ⧸ H) rfl h2' f' hf' hfyb' N
  set F := (step f (N := N))^[m]
  have hproj : ∀ s : (Fin N → V) × V, (fun i => π ((F s).1 i), π (F s).2) =
      ((fun i => π (s.1 i)), π s.2) := by
    intro s
    have hsemi : Function.Semiconj (fun s : (Fin N → V) × V => ((fun i => π (s.1 i)), π s.2))
        (step f) (step f') := fun s => (step_map s).symm
    calc ((fun i => π ((F s).1 i)), π (F s).2) = (step f')^[m] ((fun i => π (s.1 i)), π s.2) :=
          hsemi.iterate_right m s
      _ = ((fun i => π (s.1 i)), π s.2) := by rw [ihm]; rfl
  have hF : ∀ s δ : (Fin N → V) × V, (∀ i, δ.1 i ∈ H) → δ.2 ∈ H → F (s + δ) = F s + δ := by
    intro s δ hδ1 hδ2
    simp only [F]
    induction m generalizing s with
    | zero => rfl
    | succ k ihk =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, step_add s δ hδ1 hδ2,
        ihk]
  have hstate : ∀ z : (Fin N → V) × V, z + z = 0 := by
    intro z
    apply Prod.ext
    · funext i; exact h2 _
    · exact h2 _
  have hnegs : ∀ z : (Fin N → V) × V, -z = z := fun z => neg_eq_of_add_eq_zero_right (hstate z)
  funext s
  have hd1 : ∀ i, (F s - s).1 i ∈ H := by
    intro i
    have e := congrArg (fun p => p.1 i) (hproj s)
    simp only at e
    have e' := (QuotientAddGroup.eq).mp e.symm
    rw [Prod.fst_sub, Pi.sub_apply, sub_eq_neg_add]
    exact e'
  have hd2 : (F s - s).2 ∈ H := by
    have e := congrArg Prod.snd (hproj s)
    have e' := (QuotientAddGroup.eq).mp e.symm
    rw [Prod.snd_sub, sub_eq_neg_add]
    exact e'
  have hFF : F (F s) = s := by
    have e := hF s (F s - s) hd1 hd2
    rw [add_sub_cancel] at e
    rw [e, sub_eq_add_neg, hnegs, ← add_assoc, hstate, zero_add]
  rw [hcard.symm, hsplit, mul_two, Function.iterate_add_apply, id]
  exact hFF

/-- The conjecture holds: the period divides the order of the field. -/
theorem result : claim := by
  intro F _ _ _ f hf hfyb N
  rw [← Nat.card_eq_fintype_card]
  exact step_iterate_card _ F rfl (fun x => CharTwo.add_self_eq_zero x) f hf hfyb N

end D5.S3.StatisticalMechanics.CellularAutomata.YangBaxterAutomatonPeriod
