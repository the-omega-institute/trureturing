/- GID: D5/S1/Dynamics/PeriodicOrbits/CountableRealization
   generality: G
   mirror-B: D5/B/S1/Dynamics/PeriodicOrbits/CountableRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One countable permutation realizes all positive-time nonnegative Dold data. -/

import D5.S1.Dynamics.PeriodicOrbits.FiniteRealization
import Mathlib.Data.PNat.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-! Countable all-length cycles and the finite-fixed-set realization criterion. -/

set_option autoImplicit false

namespace D5.S1.Dynamics.PeriodicOrbits.CountableRealization

open Function
open D5.S1.Dynamics.PeriodicOrbits.OrbitCounting (delta)
open D5.S1.Dynamics.PeriodicOrbits.FiniteRealization

/-- All positive cycle lengths at once, with finitely many copies at each length. -/
abbrev Carrier (c : ℕ → ℕ) := Σ d : ℕ+, Fin (c d.val) × ZMod d.val

/-- Rotation on each actual cyclic component. -/
noncomputable def rotation (c : ℕ → ℕ) : Equiv.Perm (Carrier c) :=
  Equiv.sigmaCongrRight fun _ => Equiv.prodCongr (Equiv.refl _) (Equiv.addRight 1)

private theorem rotation_iterate (c : ℕ → ℕ) (n : ℕ) (d : ℕ+)
    (j : Fin (c d.val)) (z : ZMod d.val) :
    (rotation c)^[n] ⟨d, j, z⟩ = ⟨d, j, z + (n : ZMod d.val)⟩ := by
  induction n with
  | zero => simp [id]
  | succ n ih =>
    rw [iterate_succ_apply', ih]
    change (⟨d, j, z + (n : ZMod d.val) + 1⟩ : Carrier c) =
      ⟨d, j, z + ((n+1 : ℕ) : ZMod d.val)⟩
    simp [Nat.cast_add, add_assoc]

private theorem fixed_iff (c : ℕ → ℕ) (n : ℕ) (x : Carrier c) :
    (rotation c)^[n] x = x ↔ x.1.val ∣ n := by
  rcases x with ⟨d,j,z⟩
  rw [rotation_iterate]
  simp [ZMod.natCast_eq_zero_iff]

/-- Number of actual fixed points; finiteness at positive times is proved below. -/
noncomputable def fixedCard {X : Type*} (f : X → X) (n : ℕ) : ℕ :=
  Nat.card {x : X // f^[n] x = x}

private noncomputable def fixedEquiv (c : ℕ → ℕ) {n : ℕ} (hn : 0 < n) :
    {x : Carrier c // (rotation c)^[n] x = x} ≃ CycleCarrier n c where
  toFun x := ⟨⟨x.val.1.val, Nat.mem_divisors.mpr
    ⟨(fixed_iff c n x.val).mp x.property, hn.ne'⟩⟩, x.val.2⟩
  invFun y := ⟨⟨⟨y.1.val, Nat.pos_of_mem_divisors y.1.property⟩, y.2⟩,
    (fixed_iff c n _).mpr (Nat.mem_divisors.mp y.1.property).1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The carrier is countable, while each positive-time fixed set is finite. -/
theorem countable_and_locally_finite (c : ℕ → ℕ) :
    Countable (Carrier c) ∧ ∀ n : ℕ, 0 < n →
      Finite {x : Carrier c // (rotation c)^[n] x = x} := by
  constructor
  · infer_instance
  · intro n hn
    exact Finite.of_equiv _ (fixedEquiv c hn).symm

/-- All positive-time counts, for the same permutation on the same carrier. -/
theorem fixed_card (c : ℕ → ℕ) {n : ℕ} (hn : 0 < n) :
    fixedCard (rotation c) n = ∑ d ∈ n.divisors, d * c d := by
  classical
  unfold fixedCard
  rw [Nat.card_congr (fixedEquiv c hn), Nat.card_eq_fintype_card]
  change Fintype.card (Σ d : Divisor n, Fin (c d.val) × ZMod d.val) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin, ZMod.card]
  rw [show (∑ d : Divisor n, c d.val * d.val) =
    ∑ d ∈ n.divisors, c d * d from
      (Finset.sum_subtype n.divisors (fun _ => Iff.rfl) (fun d => c d * d)).symm]
  simp only [Nat.mul_comm]

/-- The transform counts whole cycles, at every positive length. -/
theorem delta_fixed_card (c : ℕ → ℕ) {n : ℕ} (hn : 0 < n) :
    delta (fixedCard (rotation c)) n = (n : ℤ) * (c n : ℤ) := by
  apply ((ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun d => (d : ℤ) * (c d : ℤ))
    (g := fun k => (fixedCard (rotation c) k : ℤ))).mp ?_) n hn
  intro k hk
  exact_mod_cast (fixed_card c hk).symm

/-- The full positive-index realization criterion for the canonical countable-cycle
model. A single multiplicity function and a single permutation work for all n. -/
theorem realization_iff (a : ℕ → ℕ) :
    (∃ c : ℕ → ℕ, ∀ n : ℕ, 0 < n → fixedCard (rotation c) n = a n) ↔
    ∀ n : ℕ, 0 < n → 0 ≤ delta a n ∧ (n : ℤ) ∣ delta a n := by
  constructor
  · rintro ⟨c,hc⟩ n hn
    have he : delta a n = delta (fixedCard (rotation c)) n := by
      unfold delta
      apply Finset.sum_congr rfl
      intro p hp
      rw [hc p.2 (Nat.pos_of_mem_divisors
        ((Nat.snd_mem_divisors_of_mem_antidiagonal hp))) ]
    rw [he, delta_fixed_card c hn]
    exact ⟨mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _), dvd_mul_right _ _⟩
  · intro h
    let c : ℕ → ℕ := fun d => (delta a d / (d : ℤ)).toNat
    have hcoeff (d : ℕ) (hd : 0 < d) : (d : ℤ) * (c d : ℤ) = delta a d := by
      dsimp [c]
      rw [Int.toNat_of_nonneg (Int.ediv_nonneg (h d hd).1 (Int.natCast_nonneg _))]
      exact Int.mul_ediv_cancel' (h d hd).2
    have hi := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
      (f := fun d => (d : ℤ) * (c d : ℤ)) (g := fun d => (a d : ℤ))).mpr
      (fun d hd => (hcoeff d hd).symm)
    refine ⟨c, fun n hn => ?_⟩
    rw [fixed_card c hn]
    exact_mod_cast hi n hn

/-- Finite divisor support makes the whole carrier finite, not merely its fixed sets. -/
theorem finite_carrier_of_support (c : ℕ → ℕ) {M : ℕ} (hM : 0 < M)
    (hs : ∀ d : ℕ, 0 < c d → d ∣ M) : Finite (Carrier c) := by
  let e : Carrier c ≃ CycleCarrier M c := {
    toFun := fun x => ⟨⟨x.1.val, Nat.mem_divisors.mpr
      ⟨hs x.1.val (Nat.zero_lt_of_lt x.2.1.isLt), hM.ne'⟩⟩, x.2⟩
    invFun := fun y => ⟨⟨y.1.val, Nat.pos_of_mem_divisors y.1.property⟩, y.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact Finite.of_equiv _ e.symm

/-- Integral Mobius transform for signed data. -/
def deltaInt (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ p ∈ n.divisorsAntidiagonal, (ArithmeticFunction.moebius p.1 : ℤ) * a p.2

/-- Every integral Dold sequence is a difference of actual countable-cycle
fixed-point sequences at all positive indices. Both positive-time fixed sets are finite. -/
theorem signed_realization (a : ℕ → ℤ)
    (ha : ∀ n : ℕ, 0 < n → (n : ℤ) ∣ deltaInt a n) :
    ∃ cp cm : ℕ → ℕ, ∀ n : ℕ, 0 < n →
      (fixedCard (rotation cp) n : ℤ) - (fixedCard (rotation cm) n : ℤ) = a n := by
  let q : ℕ → ℤ := fun d => deltaInt a d / (d : ℤ)
  let cp : ℕ → ℕ := fun d => (q d).toNat
  let cm : ℕ → ℕ := fun d => (-q d).toNat
  have hsplit (d : ℕ) : (cp d : ℤ) - (cm d : ℤ) = q d := by
    dsimp [cp,cm]
    omega
  have hcoeff (d : ℕ) (hd : 0 < d) :
      (d : ℤ) * ((cp d : ℤ) - (cm d : ℤ)) = deltaInt a d := by
    rw [hsplit]
    exact Int.mul_ediv_cancel' (ha d hd)
  have hi := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun d => (d : ℤ) * ((cp d : ℤ) - (cm d : ℤ))) (g := a)).mpr
    (fun d hd => (hcoeff d hd).symm)
  refine ⟨cp,cm,fun n hn => ?_⟩
  rw [fixed_card cp hn, fixed_card cm hn]
  push_cast
  rw [← Finset.sum_sub_distrib]
  simpa only [mul_sub] using hi n hn

/-- Necessity for every map with finite positive-time fixed sets, without assuming
that the whole carrier is finite, countable, or that the map is invertible. -/
theorem necessary {X : Type*} (f : X → X)
    (hf : ∀ n : ℕ, 0 < n → Finite {x : X // f^[n] x = x})
    {n : ℕ} (hn : 0 < n) :
    0 ≤ delta (fixedCard f) n ∧ (n : ℤ) ∣ delta (fixedCard f) n := by
  classical
  let Y := {x : X // f^[n] x = x}
  letI : Finite Y := hf n hn
  letI : Fintype Y := Fintype.ofFinite Y
  let g : Y → Y := fun x => ⟨f x.val, by
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply',x.property]⟩
  have hi : ∀ d : ℕ, ∀ x : Y, (g^[d] x).val = f^[d] x.val := by
    intro d
    induction d with
    | zero => intro x;rfl
    | succ d ih =>
      intro x
      simp only [Function.iterate_succ_apply']
      change f (g^[d] x).val = f (f^[d] x.val)
      rw [ih]
  have ht (d : ℕ) (hd : d ∣ n) :
      D5.S1.Dynamics.PeriodicOrbits.OrbitCounting.fixedCount g d = fixedCard f d := by
    let e : {x : Y // g^[d] x = x} ≃ {x : X // f^[d] x = x} := {
      toFun := fun x => ⟨x.val.val, by
        simpa only [hi] using congrArg Subtype.val x.property⟩
      invFun := fun x => ⟨⟨x.val,
        Function.isPeriodicPt_iff_minimalPeriod_dvd.mpr
          ((Function.isPeriodicPt_iff_minimalPeriod_dvd.mp x.property).trans hd)⟩,
        Subtype.ext (by rw [hi]; exact x.property)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    unfold D5.S1.Dynamics.PeriodicOrbits.OrbitCounting.fixedCount
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, Nat.card_congr e]
    rfl
  have he : delta (fixedCard f) n =
      delta (D5.S1.Dynamics.PeriodicOrbits.OrbitCounting.fixedCount g) n := by
    unfold delta
    apply Finset.sum_congr rfl
    intro p hp
    rw [ht p.2 (Nat.mem_divisors.mp
      (Nat.snd_mem_divisors_of_mem_antidiagonal hp)).1]
  rw [he,D5.S1.Dynamics.PeriodicOrbits.OrbitCounting.delta_fixed_count g hn]
  exact ⟨mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _), dvd_mul_right _ _⟩

#print axioms necessary

#print axioms finite_carrier_of_support
#print axioms signed_realization

#print axioms countable_and_locally_finite
#print axioms fixed_card
#print axioms delta_fixed_card
#print axioms realization_iff

end D5.S1.Dynamics.PeriodicOrbits.CountableRealization
