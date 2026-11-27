/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeMixedPairSkew
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeMixedPairSkew
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Upper and lower skew of the original mixed Leech pair field at every doubled exponent. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairField
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalSkewAdjoints

/-!
The original corrected-field inversion exchanges the two twisted slots.
Its finite detector-lowering sum is the BPZ transpose of the translation
exponential on the odd lattice output. The two branch signs use the full
twisted weights `(3 + M) / 2` and `(3 + K) / 2`.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairSkew

open ActualLeechHyperbolic (leechData leech_spec)
open Complex (I)
open LatticeGeneratingFieldLocality hiding paritySign
open LatticePositiveEnergy LatticeInvolution
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockGradedTrace LatticeHalfFockParityT ActualChargedAdjoint
open NativeOddTwistedIntertwiner NativeOddUpperRightSkew
open NativeMixedPairState NativeMixedPairField OriginalSkewAdjoints
open SourceBPZ.OriginalSourcePairing (sourcePairing)
open NativeFullMixedField (project)
open private project_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeFullMixedField
open private sum_projectedBasis from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairField
open private J_val mem_parity from D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
open private lowering_pow_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
open private T theta_omega_fixed from
  D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private sourceL1 from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalSkewAdjoints

local notation "ℒ" => leechData
local notation "L₁" => sourceL1 ℒ
local notation "S" => oddTranslation ℒ
local notation "Bᵥ" => sourcePairing ℒ
local notation "Bₘ" => actualForm ℒ leechUnit
private theorem hpos : Matrix.PosDef (leechData.G.map (Int.cast : ℤ → ℝ)) := leech_spec.2.2.1

attribute [local irreducible] leechData

private def lowerOdd (a : OddCarrier ℒ) (j : ℕ) : OddCarrier ℒ :=
  ⟨(L₁ ^ j) a.val, by
    induction j with
    | zero => simp [a.property]
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply]
      let w := LatticeActualConformalState.omega ℒ (LatticeSugawaraCurrents.gramComplex ℒ)⁻¹
      have hw : theta ℒ w = (1 : ℂ) • w := by
        rw [one_smul]
        exact theta_omega_fixed ℒ _
      have hm : (LatticeAllStateField.Y ℒ w)[[2]] = L₁ := by
        simpa [w] using LatticeActualConformalState.omega_modes ℒ
          (LatticeSugawaraCurrents.gramComplex ℒ)⁻¹ 1
      have h := mode_eigenvalue_selection ℒ 1 (-1)
        w ((L₁ ^ j) a.val) hw ((mem_eigenspace ℒ (-1) _).mp ih) 2
      rw [hm, one_mul] at h
      exact (mem_eigenspace ℒ (-1) _).mpr h⟩

private theorem translation_pairing (x a : OddCarrier ℒ) (j : ℕ) :
    Bᵥ ((S ^ j) x).val a.val = Bᵥ x.val (lowerOdd a j).val := by
  change _ = Bᵥ x.val ((L₁ ^ j) a.val)
  generalize a.val = y
  induction j generalizing y with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ' S, Module.End.mul_apply]
    change Bᵥ (LatticeSugawaraConformal.translation ℒ ((S ^ j) x).val) y = _
    rw [sourcePairing_translation ℒ leechUnit, ih, pow_succ L₁, Module.End.mul_apply]

private theorem translation_grade (x : OddCarrier ℒ) (d : ℤ)
    (hx : x.val ∈ grade ℒ d) (j : ℕ) : ((S ^ j) x).val ∈ grade ℒ (d + j) := by
  have hv : LatticeAllStateField.vacuum ℒ ∈ grade ℒ 0 := by
    rw [grade_zero ℒ hpos]
    exact Submodule.subset_span (Set.mem_singleton _)
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    rw [pow_succ' S, Module.End.mul_apply]
    change LatticeSugawaraConformal.translation ℒ ((S ^ j) x).val ∈ grade ℒ _
    rw [LatticeActualVertexAlgebra.translation_as_mode]
    have hm := positive_actual_mode_grade ℒ hpos (d + j) 0 (-2)
      ((S ^ j) x).val (LatticeAllStateField.vacuum ℒ) ih hv
    rwa [show d + (j : ℤ) + 0 - (-2) - 1 = d + ((j + 1 : ℕ) : ℤ) by omega] at hm

private theorem I_even_power (d : ℤ) : I ^ (2 * d) = (-1 : ℂ) ^ d := by
  rw [zpow_mul, show I ^ (2 : ℤ) = -1 by exact (zpow_natCast I 2).trans Complex.I_sq]

private theorem phase_eq_of_mod_four (x y k : ℤ) (h : x = y + 4 * k) :
    I ^ x = I ^ y := by
  have h4 : I ^ (4 : ℤ) = 1 := by
    rw [show (4 : ℤ) = 2 * 2 by decide, I_even_power]
    norm_num
  rw [h, zpow_add₀ Complex.I_ne_zero, zpow_mul I 4 k, h4, one_zpow, mul_one]

private def halfTurn (upper : Bool) (e : ℤ) : ℂ := I ^ (if upper then e else -e)

private def weightSign (upper : Bool) (M K : ℕ) : ℂ :=
  (-1) ^ (3 + if upper then M else K)

private theorem inversion_phase (upper : Bool) (M K : ℕ) (d m : ℤ) (p q j : ℕ)
    (hd : 2 * d = (M : ℤ) + K + 3 - 2 * m) :
    I ^ (-(3 + (M : ℤ))) * I ^ (-2 * ((M : ℤ) - m - q + p) - 3) * (-1 : ℂ) ^ d =
      weightSign upper M K * halfTurn upper (-2 * (m + j) - 3) *
        (I ^ (-(3 + (K : ℤ))) * I ^ (-2 * ((K : ℤ) - (m + j) - p + q) - 3)) := by
  have hs (N : ℕ) : (-1 : ℂ) ^ (3 + N) = I ^ (2 * (3 + (N : ℤ))) := by
    rw [I_even_power, ← zpow_natCast]
    push_cast
    rfl
  cases upper <;> simp only [weightSign, halfTurn, Bool.false_eq_true, ↓reduceIte, hs]
  all_goals
    simp only [← I_even_power d, ← zpow_add₀ Complex.I_ne_zero]
  · apply phase_eq_of_mod_four _ _ (d - (M : ℤ) - 3 - j + q - p)
    omega
  · apply phase_eq_of_mod_four _ _ (-(M : ℤ) + K + q - p)
    omega

/-- Reuse an actual twisted vector after exchanging the two parity slots. -/
def swapInput {s : Bool} (u : Twisted ℒ leechUnit s) : Twisted ℒ leechUnit (!(!s)) :=
  ⟨u.val, by simpa only [Bool.not_not] using u.property⟩

private theorem swapInput_val {s : Bool} (u : Twisted ℒ leechUnit s) :
    (swapInput u).val = u.val := by
  cases s <;> rfl

private theorem swapInput_zero (s : Bool) :
    swapInput (0 : Twisted ℒ leechUnit s) = 0 := by cases s <;> rfl

private theorem swapInput_add {s : Bool} (u w : Twisted ℒ leechUnit s) :
    swapInput (u + w) = swapInput u + swapInput w := by cases s <;> rfl

private theorem swapInput_smul {s : Bool} (c : ℂ) (u : Twisted ℒ leechUnit s) :
    swapInput (c • u) = c • swapInput u := by cases s <;> rfl

set_option maxHeartbeats 500000 in
private theorem state_pairing_skew (upper s : Bool) (M K : ℕ) (m d : ℤ)
    (u : Twisted ℒ leechUnit s) (v : Twisted ℒ leechUnit (!s))
    (hu : u.val ∈ actualGrade ℒ leechUnit M)
    (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (a : oddGrade d) (hd : 2 * d = (M : ℤ) + K + 3 - 2 * m) :
    Bᵥ (mixedPairState s M K m u v).val a.val =
      ∑ j ∈ Finset.range (d.toNat + 1),
        (weightSign upper M K * halfTurn upper (-2 * (m + j) - 3) *
          (j.factorial : ℂ)⁻¹) *
          Bᵥ ((S ^ j) (mixedPairState (!s) K M (m + j) v
            (swapInput u))).val a.val := by
  classical
  let a₀ : OddCarrier ℒ := ⟨a.val, a.property.2⟩
  let J := Finset.range (d.toNat + 1)
  let P := Finset.range (K / 2 + 1)
  let Q := Finset.range (M / 2 + 1)
  let r := fun p q : ℕ => -2 * ((M : ℤ) - m - q + p) - 3
  let t := fun p q j : ℕ => -2 * ((K : ℤ) - (m + j) - p + q) - 3
  let X := fun q : ℕ => (T ℒ leechUnit ^ q) u.val
  let Y := fun p : ℕ => (T ℒ leechUnit ^ p) v.val
  let f := fun p q j : ℕ =>
    (weightSign upper M K * halfTurn upper (-2 * (m + j) - 3) * (j.factorial : ℂ)⁻¹) *
      (I ^ (-(3 + (K : ℤ))) * ((p.factorial : ℂ)⁻¹ *
        ((I ^ t p q j * (q.factorial : ℂ)⁻¹) *
          Bₘ (X q) ((correctedField ℒ leechUnit (lowerOdd a₀ j).val).coeff
            (t p q j) (Y p)))))
  have hmode (p q j : ℕ) : -r p q - 4*d + 2*(j : ℤ) = t p q j := by
    dsimp [r, t]
    omega
  have hleft : Bᵥ (mixedPairState s M K m u v).val a.val =
      I ^ (-(3 + (M : ℤ))) * ∑ q ∈ Q, (q.factorial : ℂ)⁻¹ *
        ∑ p ∈ P, (I ^ r p q * (p.factorial : ℂ)⁻¹) *
          Bₘ (Y p) ((correctedField ℒ leechUnit a.val).coeff (r p q) (X q)) := by
    change Bᵥ (mixedPairState s M K m u v).val a₀.val = _
    rw [mixedPairState_pairing s M K m u v hu hv a₀,
      mixedPairing_finite s M K m u v hv a₀]
    simp only [J_val, lowering_pow_val]
    rfl
  let u' := swapInput u
  have huval : u'.val = u.val := swapInput_val u
  have hu' : u'.val ∈ actualGrade ℒ leechUnit M := huval.symm ▸ hu
  have hright (j : ℕ) :
      Bᵥ (mixedPairState (!s) K M (m + j) v u').val (lowerOdd a₀ j).val =
        I ^ (-(3 + (K : ℤ))) * ∑ p ∈ P, (p.factorial : ℂ)⁻¹ *
          ∑ q ∈ Q, (I ^ t p q j * (q.factorial : ℂ)⁻¹) *
            Bₘ (X q) ((correctedField ℒ leechUnit (lowerOdd a₀ j).val).coeff
              (t p q j) (Y p)) := by
    rw [mixedPairState_pairing (!s) K M (m + j) v u' hv hu',
      mixedPairing_finite (!s) K M (m + j) v u' hu']
    simp only [J_val, lowering_pow_val, huval]
    rfl
  calc
    _ = ∑ q ∈ Q, ∑ p ∈ P, ∑ j ∈ J, f p q j := by
      rw [hleft, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      rw [← mul_assoc, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [(ActualPairingSymmetry.actualForm_symmetric ℒ leechUnit).eq (Y p) _,
        actual_corrected_adjoint_of_grade ℒ leechUnit hpos d (r p q) a.val
          a.property.1 (X q) (Y p), ← mul_assoc, ← mul_assoc, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [hmode p q j]
      let b := Bₘ (X q) ((correctedField ℒ leechUnit (lowerOdd a₀ j).val).coeff
        (t p q j) (Y p))
      let c := (j.factorial : ℂ)⁻¹ * (q.factorial : ℂ)⁻¹ * (p.factorial : ℂ)⁻¹ * b
      change I ^ (-(3 + (M : ℤ))) * (q.factorial : ℂ)⁻¹ *
          (I ^ r p q * (p.factorial : ℂ)⁻¹) * (-1 : ℂ) ^ d *
          ((j.factorial : ℂ)⁻¹ * b) = f p q j
      have hp :
          I ^ (-(3 + (M : ℤ))) * I ^ r p q * (-1 : ℂ) ^ d =
            weightSign upper M K * halfTurn upper (-2 * (m + j) - 3) *
              (I ^ (-(3 + (K : ℤ))) * I ^ t p q j) :=
        inversion_phase upper M K d m p q j hd
      calc
        _ = (I ^ (-(3 + (M : ℤ))) * I ^ r p q * (-1 : ℂ) ^ d) * c := by dsimp only [c]; ring
        _ = _ := by rw [hp]; dsimp only [f, c, b]; ring
    _ = ∑ j ∈ J, ∑ p ∈ P, ∑ q ∈ Q, f p q j := by
      calc
        _ = ∑ q ∈ Q, ∑ j ∈ J, ∑ p ∈ P, f p q j :=
          Finset.sum_congr rfl fun q _ => Finset.sum_comm
        _ = ∑ j ∈ J, ∑ q ∈ Q, ∑ p ∈ P, f p q j := Finset.sum_comm
        _ = _ := Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      change _ = _ * Bᵥ ((S ^ j) (mixedPairState (!s) K M (m + j) v u')).val a₀.val
      rw [translation_pairing, hright, ← mul_assoc, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [← mul_assoc, Finset.mul_sum]
      simp only [f, mul_assoc]

private theorem homogeneous_sign {s : Bool} {M : ℕ} {u : Twisted ℒ leechUnit s}
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hne : u ≠ 0) :
    (-1 : ℂ) ^ (3 + M) = -paritySign s := by
  have hp := (mem_parity ℒ leechUnit _ u.val).mp u.property
  have hM : actualParity ℒ leechUnit u.val = (-1 : ℂ) ^ M • u.val :=
    actualParity_on_actualGrade ℒ leechUnit M ⟨u.val, hu⟩
  have hz : ((-1 : ℂ) ^ M - paritySign s) • u.val = 0 := by
    rw [sub_smul, ← hp, ← hM, sub_self]
  have hs := sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right
    (fun h => hne (Subtype.ext h)))
  rw [pow_add, hs]
  norm_num

private theorem homogeneous_pair_grade {s : Bool} {M K : ℕ}
    {u : Twisted ℒ leechUnit s} {v : Twisted ℒ leechUnit (!s)}
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) (m : ℤ) :
    2 * mixedPairWeight M K m = (M : ℤ) + K + 3 - 2*m := by
  have parity (r : Bool) (N : ℕ) (x : Twisted ℒ leechUnit r)
      (hx : x.val ∈ actualGrade ℒ leechUnit N) (hx0 : x ≠ 0) :
      N % 2 = if r then 1 else 0 := by
    have hs := homogeneous_sign hx hx0
    rw [pow_add] at hs
    rw [neg_one_pow_eq_pow_mod_two N] at hs
    cases r <;> simp only [paritySign, Bool.false_eq_true, ↓reduceIte] at hs ⊢
    · by_contra hn
      rw [show N % 2 = 1 by omega] at hs
      norm_num at hs
    · by_contra hn
      rw [show N % 2 = 0 by omega] at hs
      norm_num at hs
  have hM := parity s M u hu hu0
  have hK := parity (!s) K v hv hv0
  unfold mixedPairWeight
  cases s <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hM hK
  all_goals omega

private abbrev W (x : ActualTensor ℒ leechUnit) :=
  ActualEnergyRestrictedDual.maxOddWeight ℒ leechUnit x

set_option maxHeartbeats 500000 in
/-- The translation convolution terminates at the bound from the two actual
finite oscillator supports. This cutoff works on both branches. -/
theorem mu_skew_translation_tail (s : Bool) (e : ℤ)
    (u : Twisted ℒ leechUnit s) (v : Twisted ℒ leechUnit (!s)) (j : ℕ)
    (hj : e + (W u.val : ℤ) + W v.val + 6 ≤ 2 * (j : ℤ)) :
    (S ^ j) ((mu (!s) v).coeff (e - 2 * (j : ℤ)) (swapInput u)) = 0 := by
  have hb : e - 2 * (j : ℤ) ≤ -(W v.val : ℤ) - W (swapInput u).val - 6 := by
    rw [swapInput_val]
    omega
  have hz := mu_lower_truncation (!s) v (swapInput u) _ hb
  exact (congrArg (fun x : OddCarrier ℒ => (S ^ j) x) hz).trans (map_zero _)

private def skewTerm (upper s : Bool) (e : ℤ)
    (u : Twisted ℒ leechUnit s) (v : Twisted ℒ leechUnit (!s)) (j : ℕ) : OddCarrier ℒ :=
  (halfTurn upper (e - 2 * (j : ℤ)) * (j.factorial : ℂ)⁻¹) •
    (S ^ j) ((mu (!s) v).coeff (e - 2 * (j : ℤ)) (swapInput u))

private theorem skewTerm_finite (upper s : Bool) (e : ℤ)
    (u : Twisted ℒ leechUnit s) (v : Twisted ℒ leechUnit (!s)) :
    Function.HasFiniteSupport (skewTerm upper s e u v) := by
  let N := ((e + (W u.val : ℤ) + W v.val + 6) / 2 + 1).toNat
  apply (Finset.range N).finite_toSet.subset
  intro j hj
  apply Finset.mem_range.mpr
  by_contra! hout
  apply hj
  rw [skewTerm, mu_skew_translation_tail s e u v j (by dsimp [N] at hout; omega), smul_zero]

set_option maxHeartbeats 600000 in
/-- Finite upper and lower skew with the explicit signs of the input weights. -/
theorem mu_skew_of_grade (upper s : Bool) (M K : ℕ) (e : ℤ)
    (u : Twisted ℒ leechUnit s) (v : Twisted ℒ leechUnit (!s))
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K) :
    (mu s u).coeff e v =
      ((-1 : ℂ) ^ (3 + if upper then M else K)) •
        ∑ᶠ j : ℕ, (I ^ (if upper then e - 2 * (j : ℤ) else -(e - 2 * (j : ℤ))) *
          (j.factorial : ℂ)⁻¹) •
            (S ^ j) ((mu (!s) v).coeff (e - 2 * (j : ℤ)) (swapInput u)) := by
  change _ = weightSign upper M K • ∑ᶠ j, skewTerm upper s e u v j
  classical
  by_cases hu0 : u = 0
  · subst u
    simp only [skewTerm, swapInput_zero, map_zero, Pi.zero_apply, LinearMap.zero_apply,
      smul_zero, finsum_zero]
  by_cases hv0 : v = 0
  · subst v
    simp only [skewTerm, swapInput_zero, map_zero, Pi.zero_apply, LinearMap.zero_apply,
      smul_zero, finsum_zero]
  by_cases he : Even e
  · rw [mu_coeff_even_zero s e u v he, finsum_eq_zero_of_forall_eq_zero, smul_zero]
    intro j
    have hj : Even (e - 2 * (j : ℤ)) := by
      obtain ⟨k, hk⟩ := he
      exact ⟨k - j, by omega⟩
    rw [skewTerm, mu_coeff_even_zero (!s) _ v (swapInput u) hj, map_zero, smul_zero]
  obtain ⟨k, hk⟩ := Int.not_even_iff_odd.mp he
  let m := -k - 2
  have heq : e = -2 * m - 3 := by dsimp [m]; omega
  let d := mixedPairWeight M K m
  have hd : 2 * d = (M : ℤ) + K + 3 - 2 * m := homogeneous_pair_grade hu hv hu0 hv0 m
  have hrev (j : ℕ) :
      (mu (!s) v).coeff (e - 2 * (j : ℤ)) (swapInput u) =
        mixedPairState (!s) K M (m + j) v (swapInput u) := by
    rw [show e - 2 * (j : ℤ) = -2 * (m + j) - 3 by omega]
    have hu' : (swapInput u).val ∈ actualGrade ℒ leechUnit M := (swapInput_val u).symm ▸ hu
    exact mu_coeff_of_grade (!s) K M (m + j) v (swapInput u) hv hu'
  have hterm (j : ℕ) (hj : d ≤ (j : ℤ)) : skewTerm upper s e u v j = 0 := by
    rw [skewTerm, hrev, mixedPairState_truncation (!s) K M (m + j) v (swapInput u) (by omega),
      map_zero, smul_zero]
  rw [heq, mu_coeff_of_grade s M K m u v hu hv]
  by_cases hnonpos : d ≤ 0
  · rw [mixedPairState_truncation s M K m u v (by omega),
      finsum_eq_zero_of_forall_eq_zero, smul_zero]
    intro j
    rw [← heq]
    exact hterm j (by omega)
  rw [← heq, finsum_eq_sum_of_support_subset (skewTerm upper s e u v)
    (show Function.support (skewTerm upper s e u v) ⊆
        (Finset.range (d.toNat + 1) : Set ℕ) from by
      intro j hj
      apply Finset.mem_range.mpr
      by_contra! hout
      exact hj (hterm j (by omega)))]
  rw [Finset.smul_sum]
  let rhs := ∑ j ∈ Finset.range (d.toNat + 1),
    weightSign upper M K • skewTerm upper s e u v j
  have hrhs : rhs.val ∈ grade ℒ d := by
    simp only [rhs, Submodule.coe_sum, Submodule.coe_smul]
    apply (grade ℒ d).sum_mem
    intro j _
    apply (grade ℒ d).smul_mem
    rw [skewTerm, hrev, Submodule.coe_smul]
    apply (grade ℒ d).smul_mem
    have hj := translation_grade (mixedPairState (!s) K M (m + j) v (swapInput u))
      (mixedPairWeight K M (m + j)) (mixedPairState_grade (!s) K M (m + j) v (swapInput u)) j
    rwa [show mixedPairWeight K M (m + j) + (j : ℤ) = d by unfold mixedPairWeight; omega] at hj
  let lhsGrade : oddGrade d := ⟨_, mixedPairState_grade s M K m u v,
    (mixedPairState s M K m u v).property⟩
  let rhsGrade : oddGrade d := ⟨rhs.val, hrhs, rhs.property⟩
  apply Subtype.ext
  change lhsGrade.val = rhsGrade.val
  apply congrArg (fun z : oddGrade d => z.val)
  apply sub_eq_zero.mp
  apply (oddGradePairing_nondegenerate d).1
  intro a
  simp only [map_sub, LinearMap.sub_apply]
  apply sub_eq_zero.mpr
  change Bᵥ (mixedPairState s M K m u v).val a.val = Bᵥ rhs.val a.val
  simp only [rhs, skewTerm, hrev, Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, ← mul_assoc]
  simpa only [heq, show ∀ j : ℕ, -2 * m - 3 - 2 * (j : ℤ) = -2 * (m + j) - 3 by intro j; ring] using
    state_pairing_skew upper s M K m d u v hu hv a hd

private def skewSum (upper s : Bool) (e : ℤ) :
    Twisted ℒ leechUnit s →ₗ[ℂ] Twisted ℒ leechUnit (!s) →ₗ[ℂ] OddCarrier ℒ :=
  LinearMap.mk₂ ℂ (fun u v => ∑ᶠ j, skewTerm upper s e u v j)
    (fun u₁ u₂ v => by
      simp only [skewTerm, swapInput_add, map_add, smul_add]
      exact finsum_add_distrib (skewTerm_finite upper s e u₁ v)
        (skewTerm_finite upper s e u₂ v))
    (fun c u v => by
      simpa only [skewTerm, swapInput_smul, map_smul, smul_comm c] using
        (smul_finsum c (skewTerm upper s e u v)).symm)
    (fun u v₁ v₂ => by
      simp only [skewTerm, map_add, Pi.add_apply, LinearMap.add_apply, smul_add]
      exact finsum_add_distrib (skewTerm_finite upper s e u v₁)
        (skewTerm_finite upper s e u v₂))
    (fun c u v => by
      simpa only [skewTerm, map_smul, Pi.smul_apply, LinearMap.smul_apply, smul_comm c] using
        (smul_finsum c (skewTerm upper s e u v)).symm)

set_option maxHeartbeats 500000 in
private theorem grade_skew_with_parity_sign (upper s : Bool) (M K : ℕ) (e : ℤ)
    (u : Twisted ℒ leechUnit s) (v : Twisted ℒ leechUnit (!s))
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K) :
    (mu s u).coeff e v = (-paritySign (if upper then s else !s)) • skewSum upper s e u v := by
  by_cases hu0 : u = 0
  · simp [hu0]
  by_cases hv0 : v = 0
  · simp [hv0]
  have law := mu_skew_of_grade upper s M K e u v hu hv
  change _ = weightSign upper M K • skewSum upper s e u v at law
  have hs : weightSign upper M K = -paritySign (if upper then s else !s) := by
    cases upper
    · exact homogeneous_sign hv hv0
    · exact homogeneous_sign hu hu0
  rwa [hs] at law

private abbrev ambientBasis := actualAmbientBasis ℒ leechUnit

private theorem projected_basis_grade (s : Bool) (i : _) :
    (project s (ambientBasis i)).val ∈ actualGrade ℒ leechUnit (oddWeight ℒ i.1) := by
  have hi : ambientBasis i ∈ actualGrade ℒ leechUnit (oddWeight ℒ i.1) := by
    simpa only [actualGrade, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero, Prod.eta] using
        actual_basis_eigenvalue ℒ leechUnit i.1 i.2
  rw [project_val]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ hi (Submodule.smul_mem _ _
    (actualParity_preserves_grade ℒ leechUnit _ _ hi)))

set_option maxHeartbeats 600000 in
/-- Upper (`upper = true`) and lower (`upper = false`) skew at every doubled
exponent of the actual mixed pair, in both input orders. The sign is the
weight sign of the first input on the upper branch and of the second input
on the lower branch. Statewise lower truncation makes the sum finite. -/
theorem mu_skew (upper s : Bool) (e : ℤ)
    (u : Twisted ℒ leechUnit s) (v : Twisted ℒ leechUnit (!s)) :
    (mu s u).coeff e v =
      (-paritySign (if upper then s else !s)) •
        ∑ᶠ j : ℕ, (I ^ (if upper then e - 2 * (j : ℤ) else -(e - 2 * (j : ℤ))) *
          (j.factorial : ℂ)⁻¹) •
            (S ^ j) ((mu (!s) v).coeff (e - 2 * (j : ℤ)) (swapInput u)) := by
  classical
  change _ = (-paritySign (if upper then s else !s)) • skewSum upper s e u v
  let F : Twisted ℒ leechUnit s →ₗ[ℂ] Twisted ℒ leechUnit (!s) →ₗ[ℂ] OddCarrier ℒ :=
    (LinearMap.proj e).comp (HVertexOperator.coeff.comp (mu s))
  let G := (-paritySign (if upper then s else !s)) • skewSum upper s e
  change F u v = G u v
  have hexpand (A : Twisted ℒ leechUnit s →ₗ[ℂ]
      Twisted ℒ leechUnit (!s) →ₗ[ℂ] OddCarrier ℒ) :
      A u v = ∑ i ∈ (ambientBasis.repr u.val).support, ambientBasis.repr u.val i •
        ∑ j ∈ (ambientBasis.repr v.val).support, ambientBasis.repr v.val j •
          A (project s (ambientBasis i)) (project (!s) (ambientBasis j)) := by
    conv_lhs =>
      rw [← sum_projectedBasis s u, ← sum_projectedBasis (!s) v]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum]
    rw [Finset.sum_comm]
    simp only [smul_comm (ambientBasis.repr v.val _)]
  rw [hexpand F, hexpand G]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun x : OddCarrier ℒ => ambientBasis.repr u.val i • x)
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun x : OddCarrier ℒ => ambientBasis.repr v.val j • x)
  exact grade_skew_with_parity_sign upper s _ _ e
    (project s (ambientBasis i)) (project (!s) (ambientBasis j))
    (projected_basis_grade s i) (projected_basis_grade (!s) j)

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairSkew
