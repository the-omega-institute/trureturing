/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldTensorBPZ
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldTensorBPZ
   mirror-E: none(waiver:algebraic-original-orbifold-tensor-field)
   anchors: []
   utility: none
   digest: BPZ transpose for the actual signed matter convolution and primary zero mode. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldPureC1Bracket
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldMatterGrading
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldCoefficientBPZ
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Batteries.Tactic.OpenPrivate

/-! BPZ for the original tensor field and the weight-one primary zero mode. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.NativeBPZ

open ActualLeechHyperbolic (leechData leech_spec)
open ActualLeechOrbifoldMatter (Orbifold leechUnit leechPosDef)
open ActualLeechOrbifoldCriticalMatter (Matter matter hyperbolicPlane hyperbolicMatter)
open RelativeBracket (matterMode matterModeTerm matterModeTerm_finite matterModeTerm_tmul
  matterZeroMode)
open LatticeGeneratingFieldLocality (Carrier)
open LatticeSugawaraCurrents (gramComplex sugawaraMode)
open LatticePositiveEnergy (actualL0_eigen_iff_grade)
open LatticeHalfFockFiniteCorrection (sourceWeight)
open LatticeHalfFockGradedTrace (actualTensorL0)
open SourceBPZ.OriginalSourcePairing (sourcePairing)
open SourceBPZ.AllStateTranspose (sourcePairing_allState)
open TwistedGround.MixedIntertwiner (integer_energy_zero)
open private plane_inverse from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldCriticalMatter
open private orbL1_pow fixedL1_pow_val lowered_twisted_energy from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldCoefficientBPZ

local notation "Plane" => Carrier hyperbolicPlane
local notation "orbL" => ActualLeechOrbifoldMatter.mode
local notation "planeL" => hyperbolicMatter.mode
local notation "OY" =>
  TwistedGround.Orbifold.OriginalOrbifoldField.Y leechData leechUnit leechPosDef
local notation "PY" => LatticeAllStateField.Y hyperbolicPlane
local notation "PB" => sourcePairing hyperbolicPlane

private theorem matterPairing_tmul (u v : Orbifold) (a b : Plane) :
    matterPairing (u ⊗ₜ[ℂ] a) (v ⊗ₜ[ℂ] b) = orbifoldPairing u v * PB a b := by
  change PB a b * orbifoldPairing u v = _
  exact mul_comm _ _

private theorem support_subset_range {V : Type*} [Zero V] (f : ℕ → V) (N : ℕ)
    (h : ∀ j, N ≤ j → f j = 0) : Function.support f ⊆ (↑(Finset.range N) : Set ℕ) := by
  intro j hj
  apply Finset.mem_range.mpr
  by_contra hN
  exact hj (h j (le_of_not_gt hN))

private theorem orbifold_lowering_bound (h : ℤ) (u : Orbifold)
    (hu : orbL 0 u = (h : ℂ) • u) :
    ∃ A : ℕ, ∀ j : ℕ, A ≤ j → (orbL 1 ^ j) u = 0 := by
  classical
  let A := u.1.val.support.sup (fun α => MvPolynomial.weightedTotalDegree
    (sourceWeight leechData) (u.1.val α)) + 1
  have e : actualTensorL0 leechData leechUnit u.2.val = (h : ℂ) • u.2.val :=
    (congrArg Prod.snd (ActualLeechOrbifoldMatter.mode_apply 0 u)).symm.trans
      (congrArg (fun w : Orbifold => w.2.val) hu)
  refine ⟨max A h.toNat, fun j hj => ?_⟩
  rw [orbL1_pow]
  apply Prod.ext
  · apply Subtype.ext
    rw [fixedL1_pow_val]
    exact Module.End.pow_map_zero_of_le ((le_max_left A h.toNat).trans hj)
      (SourceMobius.actual_sugawara_one_bound leechData leechUnit u.1.val)
  · apply Subtype.ext
    have hj' : h.toNat ≤ j := (le_max_right A h.toNat).trans hj
    exact integer_energy_zero leechData leechUnit leech_spec.1 _ _
      (lowered_twisted_energy h u.2 e j) (by omega)

private def planeLoweringBound (a : Plane) : ℕ :=
  a.support.sup (fun α => MvPolynomial.weightedTotalDegree (sourceWeight hyperbolicPlane) (a α)) + 1

private theorem plane_lowering_tail (a : Plane) (j : ℕ) (hj : planeLoweringBound a ≤ j) :
    (planeL 1 ^ j) a = 0 := by
  have hu : IsUnit hyperbolicPlane.G.det :=
    Matrix.isUnit_det_of_left_inverse OrderedHyperbolicExtension.U_mul_U
  have ha := Module.End.pow_map_zero_of_le hj
    (SourceMobius.actual_sugawara_one_bound hyperbolicPlane hu a)
  change (sugawaraMode hyperbolicPlane (gramComplex hyperbolicPlane) 1 ^ j) a = 0
  simpa only [Matrix.inv_eq_left_inv plane_inverse] using ha

/-- BPZ for the original indefinite hyperbolic lattice, with signed source weight. -/
theorem hyperbolicPairing_coefficient_transpose (p m : ℤ) (a b c : Plane)
    (ha : planeL 0 a = (p : ℂ) • a) :
    PB (((PY a)[[m]]) b) c =
      (-1 : ℂ) ^ p * ∑ j ∈ Finset.range (planeLoweringBound a),
        (j.factorial : ℂ)⁻¹ * PB b (((PY ((planeL 1 ^ j) a))[[2 * p - m - j - 2]]) c) := by
  have hu : IsUnit hyperbolicPlane.G.det :=
    Matrix.isUnit_det_of_left_inverse OrderedHyperbolicExtension.U_mul_U
  have hg := (actualL0_eigen_iff_grade hyperbolicPlane _ plane_inverse plane_inverse p a).mp ha
  rw [show planeL 1 = sugawaraMode hyperbolicPlane (gramComplex hyperbolicPlane) 1 from rfl]
  simpa only [planeLoweringBound, Matrix.inv_eq_left_inv plane_inverse,
    sub_right_comm (2 * p : ℤ) (_ : ℤ) m] using
    sourcePairing_allState hyperbolicPlane hu p m a hg b c

private def loweringPair (h n : ℤ) (φ ψ χ : Matter) (s : ℕ) : ℂ :=
  (s.factorial : ℂ)⁻¹ *
    matterPairing ψ (matterMode (2 * h - n - s - 2) ((matter.mode 1 ^ s) φ) χ)

private theorem loweringPair_zero (h n : ℤ) (φ ψ χ : Matter) (s : ℕ)
    (hs : (matter.mode 1 ^ s) φ = 0) : loweringPair h n φ ψ χ s = 0 := by
  simp [loweringPair, hs]

private theorem rectangle_sum (A B N : ℕ) (hN : A + B ≤ N) (f : ℕ × ℕ → ℂ)
    (tail : ∀ q : ℕ × ℕ, A ≤ q.1 ∨ B ≤ q.2 → f q = 0) :
    (∑ j ∈ Finset.range A, ∑ l ∈ Finset.range B, f (j, l)) =
      ∑ s ∈ Finset.range N, ∑ q ∈ Finset.HasAntidiagonal.antidiagonal s, f q := by
  classical
  let R := (Finset.range A) ×ˢ (Finset.range B)
  have into : ∀ q ∈ R, q.1 + q.2 ∈ Finset.range N := by
    intro q hq
    obtain ⟨hj, hl⟩ := Finset.mem_product.mp hq
    exact Finset.mem_range.mpr (by
      have := Finset.mem_range.mp hj
      have := Finset.mem_range.mp hl
      omega)
  calc
    (∑ j ∈ Finset.range A, ∑ l ∈ Finset.range B, f (j, l)) =
        ∑ q ∈ R, f q := (Finset.sum_product _ _ f).symm
    ∑ q ∈ R, f q =
        ∑ s ∈ Finset.range N, ∑ q ∈ R.filter (fun q => q.1 + q.2 = s), f q :=
      (Finset.sum_fiberwise_of_maps_to into f).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_subset
      · intro q hq
        exact Finset.HasAntidiagonal.mem_antidiagonal.mpr (Finset.mem_filter.mp hq).2
      · intro q hq hn
        apply tail
        by_contra hn'
        push Not at hn'
        exact hn (Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr
              ⟨Finset.mem_range.mpr hn'.1, Finset.mem_range.mpr hn'.2⟩,
            Finset.HasAntidiagonal.mem_antidiagonal.mp hq⟩)

private theorem factorial_weight (s j l : ℕ) (h : j + l = s) :
    (s.factorial : ℂ)⁻¹ * (s.choose j : ℂ) =
      (j.factorial : ℂ)⁻¹ * (l.factorial : ℂ)⁻¹ := by
  subst s
  have e : (((j + l).choose j : ℕ) : ℂ) * (j.factorial : ℂ) * (l.factorial : ℂ) =
      ((j + l).factorial : ℂ) := by
    have eNat := Nat.choose_mul_factorial_mul_factorial (n := j + l) (k := j) (by omega)
    rw [Nat.add_sub_cancel_left] at eNat
    exact_mod_cast eNat
  have hj : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero j)
  have hl : (l.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero l)
  have hs : ((j + l).factorial : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero (j + l))
  field_simp [hj, hl, hs]
  linear_combination e

set_option maxHeartbeats 2000000 in
-- The finite convolution compares the two concrete tensor field coefficient maps.
private theorem pure_bpz_finite (h p n : ℤ) (u : Orbifold) (a : Plane)
    (hu : orbL 0 u = (h : ℂ) • u) (ha : planeL 0 a = (p : ℂ) • a)
    (A N : ℕ) (huA : ∀ j : ℕ, A ≤ j → (orbL 1 ^ j) u = 0)
    (hN : A + planeLoweringBound a ≤ N)
    (v w : Orbifold) (b c : Plane) :
    matterPairing (matterMode n (u ⊗ₜ[ℂ] a) (v ⊗ₜ[ℂ] b)) (w ⊗ₜ[ℂ] c) =
      (-1 : ℂ) ^ (h + p) *
        ∑ s ∈ Finset.range N, loweringPair (h + p) n (u ⊗ₜ[ℂ] a)
          (v ⊗ₜ[ℂ] b) (w ⊗ₜ[ℂ] c) s := by
  classical
  let B := planeLoweringBound a
  let x : Matter := v ⊗ₜ[ℂ] b
  let y : Matter := w ⊗ₜ[ℂ] c
  let U (j : ℕ) := (orbL 1 ^ j) u
  let P (l : ℕ) := (planeL 1 ^ l) a
  let shift (j : ℕ) (k : ℤ) := 2 * h - k - (j : ℤ) - 2
  let out (s : ℕ) := 2 * (h + p) - n - (s : ℤ) - 2
  let J (j l : ℕ) := (j.factorial : ℂ)⁻¹ * (l.factorial : ℂ)⁻¹
  let G (j l : ℕ) (k : ℤ) :=
    J j l * matterPairing x (matterModeTerm (out (j + l)) k (U j ⊗ₜ[ℂ] P l) y)
  let F (j l : ℕ) (k : ℤ) := G j l (shift j k)
  let H (j l : ℕ) :=
    J j l * matterPairing x (matterMode (out (j + l)) (U j ⊗ₜ[ℂ] P l) y)
  have orbBPZ (k : ℤ) := orbifoldPairing_coefficient_transpose h k u v w hu
  have orbSum (k : ℤ) :
      orbifoldPairing (((OY u)[[k]]) v) w =
        (-1 : ℂ) ^ h * ∑ j ∈ Finset.range A, (j.factorial : ℂ)⁻¹ *
          orbifoldPairing v (((OY (U j))[[shift j k]]) w) := by
    rw [orbBPZ k]
    congr 1
    apply finsum_eq_finsetSum_of_support_subset
    apply support_subset_range
    intro j hj
    simp [huA j hj]
  have point (k : ℤ) :
      matterPairing (matterModeTerm n k (u ⊗ₜ[ℂ] a) x) y =
        (-1 : ℂ) ^ (h + p) *
          ∑ j ∈ Finset.range A, ∑ l ∈ Finset.range B, F j l k := by
    dsimp only [x, y]
    rw [matterModeTerm_tmul, matterPairing_tmul, orbSum,
      hyperbolicPairing_coefficient_transpose p (n - 1 - k) a b c ha,
      zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    dsimp only [B]
    let O := ∑ j ∈ Finset.range A, (j.factorial : ℂ)⁻¹ *
      orbifoldPairing v (((OY (U j))[[shift j k]]) w)
    let L := ∑ l ∈ Finset.range (planeLoweringBound a), (l.factorial : ℂ)⁻¹ *
      PB b (((PY (P l))[[2 * p - (n - 1 - k) - l - 2]]) c)
    change ((-1 : ℂ) ^ h * O) * ((-1 : ℂ) ^ p * L) = _
    calc
      _ = ((-1 : ℂ) ^ h * (-1 : ℂ) ^ p) * (O * L) := by ring
      _ = _ := by
        congr 1
        dsimp only [O, L]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        dsimp only [F, G, x, y, J]
        rw [matterModeTerm_tmul, matterPairing_tmul,
          show out (j + l) - 1 - shift j k = 2 * p - (n - 1 - k) - l - 2 by
            dsimp [out, shift]
            push_cast
            ring]
        ring
  have finiteG (j l : ℕ) : Function.HasFiniteSupport (G j l) := by
    apply (matterModeTerm_finite (out (j + l)) (U j ⊗ₜ[ℂ] P l) y).subset
    intro k hk
    by_contra he
    apply hk
    have hz : matterModeTerm (out (j + l)) k (U j ⊗ₜ[ℂ] P l) y = 0 := not_ne_iff.mp he
    simp [G, hz]
  have shift_inv (j : ℕ) : Function.Involutive (shift j) := by
    intro k
    dsimp [shift]
    omega
  have finiteF (j l : ℕ) : Function.HasFiniteSupport (F j l) := by
    change (shift j ⁻¹' Function.support (G j l)).Finite
    exact Set.Finite.preimage (shift_inv j).injective.injOn (finiteG j l)
  have finite_sum (j : ℕ) :
      Function.HasFiniteSupport (fun k : ℤ => ∑ l ∈ Finset.range B, F j l k) := by
    classical
    apply ((Finset.range B).finite_toSet.biUnion fun l _ => finiteF j l).subset
    intro k hk
    by_contra he
    apply hk
    apply Finset.sum_eq_zero
    intro l hl
    by_contra hl'
    exact he (Set.mem_iUnion₂.mpr ⟨l, hl, hl'⟩)
  have reindex (j l : ℕ) : (∑ᶠ k : ℤ, F j l k) = H j l := by
    change (∑ᶠ k : ℤ, G j l (shift j k)) = _
    rw [finsum_comp _ (shift_inv j).bijective]
    unfold H G
    let t (k : ℤ) := matterModeTerm (out (j + l)) k (U j ⊗ₜ[ℂ] P l) y
    have ht : Function.HasFiniteSupport t :=
      matterModeTerm_finite (out (j + l)) (U j ⊗ₜ[ℂ] P l) y
    have hb : Function.HasFiniteSupport (fun k => matterPairing x (t k)) :=
      ht.subset (fun k hk hz => hk (by simp [hz]))
    change (∑ᶠ k : ℤ, J j l * matterPairing x (t k)) =
      J j l * matterPairing x (∑ᶠ k : ℤ, t k)
    rw [← mul_finsum' _ _ hb, ← map_finsum (matterPairing x) ht]
  have tail (q : ℕ × ℕ) (hq : A ≤ q.1 ∨ B ≤ q.2) : H q.1 q.2 = 0 := by
    rcases hq with hj | hl
    · simp [H, U, huA q.1 hj]
    · simp [H, P, plane_lowering_tail a q.2 hl]
  have diagonal (s : ℕ) :
      (∑ q ∈ Finset.HasAntidiagonal.antidiagonal s, H q.1 q.2) =
        loweringPair (h + p) n (u ⊗ₜ[ℂ] a) x y s := by
    unfold loweringPair
    rw [matter_L1_pow_tmul, map_sum]
    simp only [LinearMap.sum_apply, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hq
    rw [← Nat.cast_smul_eq_nsmul ℂ]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    dsimp only [H, J, out, U, P]
    rw [hs, ← factorial_weight s q.1 q.2 hs]
    ring
  change matterPairing (matterMode n (u ⊗ₜ[ℂ] a) x) y =
    (-1 : ℂ) ^ (h + p) * ∑ s ∈ Finset.range N,
      loweringPair (h + p) n (u ⊗ₜ[ℂ] a) x y s
  change (matterPairing.flip y) (∑ᶠ k : ℤ, matterModeTerm n k (u ⊗ₜ[ℂ] a) x) = _
  rw [map_finsum (matterPairing.flip y) (matterModeTerm_finite n (u ⊗ₜ[ℂ] a) x)]
  change (∑ᶠ k : ℤ, matterPairing (matterModeTerm n k (u ⊗ₜ[ℂ] a) x) y) = _
  rw [show (fun k : ℤ => matterPairing (matterModeTerm n k (u ⊗ₜ[ℂ] a) x) y) =
    (fun k : ℤ => (-1 : ℂ) ^ (h + p) *
      ∑ j ∈ Finset.range A, ∑ l ∈ Finset.range B, F j l k) from funext point]
  rw [← mul_finsum, finsum_sum_comm (Finset.range A) _ (fun j _ => finite_sum j)]
  congr 1
  calc
    _ = ∑ j ∈ Finset.range A, ∑ l ∈ Finset.range B, H j l := by
      apply Finset.sum_congr rfl
      intro j _
      rw [finsum_sum_comm (Finset.range B) _ (fun l _ => finiteF j l)]
      exact Finset.sum_congr rfl fun l _ => reindex j l
    _ = ∑ s ∈ Finset.range N, ∑ q ∈ Finset.HasAntidiagonal.antidiagonal s, H q.1 q.2 :=
      rectangle_sum A B N hN (fun q => H q.1 q.2) tail
    _ = _ := Finset.sum_congr rfl fun s _ => diagonal s

/-- All coefficients on a pure tensor source of signed integer factor weights.
The paired arguments are arbitrary matter tensors. -/
theorem matterPairing_coefficient_transpose_tmul (h p n : ℤ) (u : Orbifold) (a : Plane)
    (hu : orbL 0 u = (h : ℂ) • u) (ha : planeL 0 a = (p : ℂ) • a)
    (ψ χ : Matter) :
    matterPairing (matterMode n (u ⊗ₜ[ℂ] a) ψ) χ =
      (-1 : ℂ) ^ (h + p) * ∑ᶠ s : ℕ, (s.factorial : ℂ)⁻¹ *
        matterPairing ψ (matterMode (2 * (h + p) - n - s - 2)
          ((matter.mode 1 ^ s) (u ⊗ₜ[ℂ] a)) χ) := by
  obtain ⟨A, hA⟩ := orbifold_lowering_bound h u hu
  let N := A + planeLoweringBound a
  let φ : Matter := u ⊗ₜ[ℂ] a
  have htail : ∀ s : ℕ, N ≤ s → (matter.mode 1 ^ s) φ = 0 :=
    fun s hs => matter_L1_pow_tmul_eq_zero A (planeLoweringBound a) s u a hA
      (plane_lowering_tail a) hs
  change matterPairing (matterMode n φ ψ) χ =
    (-1 : ℂ) ^ (h + p) * ∑ᶠ s : ℕ, loweringPair (h + p) n φ ψ χ s
  rw [finsum_eq_finsetSum_of_support_subset _
    (support_subset_range _ N (fun s hs => loweringPair_zero _ _ _ _ _ s (htail s hs)))]
  induction ψ using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [loweringPair, map_add, LinearMap.add_apply, mul_add, Finset.sum_add_distrib]
      at hx hy ⊢
    rw [hx, hy]
  | tmul v b =>
    induction χ using TensorProduct.inductionOn with
    | add x y hx hy =>
      simp only [loweringPair, map_add, mul_add, Finset.sum_add_distrib] at hx hy ⊢
      rw [hx, hy]
    | tmul w c => exact pure_bpz_finite h p n u a hu ha A N hA (le_refl N) v w b c

/-- BPZ for the literal matter convolution at every signed integer L0 weight. -/
theorem matterPairing_coefficient_transpose (h n : ℤ) (φ ψ χ : Matter)
    (hφ : matter.mode 0 φ = (h : ℂ) • φ) :
    matterPairing (matterMode n φ ψ) χ =
      (-1 : ℂ) ^ h * ∑ᶠ s : ℕ, (s.factorial : ℂ)⁻¹ *
        matterPairing ψ (matterMode (2 * h - n - s - 2) ((matter.mode 1 ^ s) φ) χ) := by
  have hh : φ ∈ Submodule.span ℂ (homogeneousMatterTensors h) := by
    rw [← matter_eigenspace_eq_span]
    exact Module.End.mem_eigenspace_iff.mpr hφ
  let f (x : Matter) := loweringPair h n x ψ χ
  have hfinite (x : Matter) (N : ℕ) (hx : ∀ s : ℕ, N ≤ s → (matter.mode 1 ^ s) x = 0) :
      Function.HasFiniteSupport (f x) :=
    (Finset.range N).finite_toSet.subset
      (support_subset_range _ N (fun s hs => loweringPair_zero _ _ _ _ _ s (hx s hs)))
  change matterPairing (matterMode n φ ψ) χ = (-1 : ℂ) ^ h * ∑ᶠ s : ℕ, f φ s
  have claim (x : Matter) (hx : x ∈ Submodule.span ℂ (homogeneousMatterTensors h)) :
      (∃ N : ℕ, ∀ s : ℕ, N ≤ s → (matter.mode 1 ^ s) x = 0) ∧
        matterPairing (matterMode n x ψ) χ = (-1 : ℂ) ^ h * ∑ᶠ s : ℕ, f x s := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, q, u, a, he, hu, ha, rfl⟩ := hx
      obtain ⟨A, hA⟩ := orbifold_lowering_bound p u hu
      refine ⟨⟨A + planeLoweringBound a, fun s hs =>
        matter_L1_pow_tmul_eq_zero A (planeLoweringBound a) s u a hA
          (plane_lowering_tail a) hs⟩, ?_⟩
      simpa only [f, loweringPair, he] using
        matterPairing_coefficient_transpose_tmul p q n u a hu ha ψ χ
    | zero => exact ⟨⟨0, fun s _ => map_zero _⟩, by simp [f, loweringPair]⟩
    | add x y _ _ hx hy =>
      obtain ⟨⟨A, hA⟩, hx⟩ := hx
      obtain ⟨⟨B, hB⟩, hy⟩ := hy
      refine ⟨⟨max A B, fun s hs => by
        rw [map_add, hA s ((le_max_left A B).trans hs),
          hB s ((le_max_right A B).trans hs), add_zero]⟩, ?_⟩
      have hadd : f (x + y) = f x + f y := by
        funext s
        simp only [f, loweringPair, Pi.add_apply, map_add, LinearMap.add_apply, mul_add]
      rw [map_add, LinearMap.add_apply, map_add, LinearMap.add_apply, hx, hy, hadd]
      simp only [Pi.add_apply, finsum_add_distrib (hfinite x A hA) (hfinite y B hB), mul_add]
    | smul c x _ hx =>
      obtain ⟨⟨A, hA⟩, hx⟩ := hx
      refine ⟨⟨A, fun s hs => by rw [map_smul, hA s hs, smul_zero]⟩, ?_⟩
      have hsmul : f (c • x) = c • f x := by
        funext s
        simp only [f, loweringPair, Pi.smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
        ring
      rw [map_smul, LinearMap.smul_apply, map_smul, LinearMap.smul_apply, hx, hsmul]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← mul_finsum' (f x) c (hfinite x A hA)]
      ring
  exact (claim φ hh).2

/-- The zero mode of every actual weight-one matter state killed by total L1
is skew for the native matter BPZ form. -/
theorem matterPairing_matterZeroMode_skew (φ ψ χ : Matter)
    (h₀ : matter.mode 0 φ = φ) (h₁ : matter.mode 1 φ = 0) :
    matterPairing (matterZeroMode φ ψ) χ = -matterPairing ψ (matterZeroMode φ χ) := by
  have h := matterPairing_coefficient_transpose 1 0 φ ψ χ (by simpa using h₀)
  have hsupport : Function.support (loweringPair 1 0 φ ψ χ) ⊆
      (↑(Finset.range 1) : Set ℕ) := by
    apply support_subset_range
    intro s hs
    apply loweringPair_zero
    exact Module.End.pow_map_zero_of_le hs (by simpa using h₁)
  change matterPairing (matterMode 0 φ ψ) χ =
    (-1 : ℂ) ^ (1 : ℤ) * ∑ᶠ s : ℕ, loweringPair 1 0 φ ψ χ s at h
  rw [finsum_eq_finsetSum_of_support_subset _ hsupport] at h
  simpa [loweringPair, matterZeroMode, zpow_one] using h

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.NativeBPZ
