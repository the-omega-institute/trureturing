/- GID: D5/S3/VertexAlgebra/TwistedGround/MixedJacobiCommonCube
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/MixedJacobiCommonCube
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Common-cube contraction of both actual signed branches and target-grade pairing. -/
import D5.S3.VertexAlgebra.TwistedGround.MixedJacobiCoefficients

/-! Actual lowering support places both signed input branches and the
dual-action branch in one finite cube before source-law cancellation. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators VertexOperator DirectSum
namespace D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockGradedTrace
open LatticeHalfFockFiniteCorrection (sourceWeight)
open LatticeAllStateField LatticePositiveEnergy LatticeInvolution
open ActualChargedAdjoint LatticeSugawaraCurrents LatticeSugawaraVirasoro
open HalfFock.LatticeHalfFockParityField
open private T originalL1 original_l1_grade
  from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner

private def sourceLoweringCutoff (D : LatticeData) (a : Carrier D) : ℕ :=
  a.support.sup (fun c => MvPolynomial.weightedTotalDegree
    (LatticeHalfFockFiniteCorrection.sourceWeight D) (a c))+1

private theorem source_lowering_zero (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Carrier D) (L : ℕ) (hL : sourceLoweringCutoff D a ≤ L) :
    (originalL1 D ^ L) a = 0 := by
  have killed : (originalL1 D ^ sourceLoweringCutoff D a) a = 0 :=
    SourceMobius.actual_sugawara_one_bound D hu a
  rw [show L = (L-sourceLoweringCutoff D a)+sourceLoweringCutoff D a by omega,
    pow_add, Module.End.mul_apply, killed, map_zero]

private theorem phase_even_shift (x t : ℤ) :
    (-1 : ℂ)^(x+2*t) = (-1 : ℂ)^x := by
  rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_mul]
  norm_num

private def mixedCommonWeight (H : ℕ) (d n : ℤ) (p q L : ℕ) : ℂ :=
  (-1 : ℂ)^(n+1-(p : ℤ)-(H : ℤ)+(q : ℤ)+d) /
    ((p.factorial : ℂ)*(q.factorial : ℂ)*(L.factorial : ℂ))

private theorem first_input_common_phase (H : ℕ) (d m n r : ℤ) (p q L : ℕ) :
    ((-1 : ℂ)^(m+n+r+2-(p : ℤ)-(H : ℤ)-d+(q : ℤ)+(L : ℤ))) /
        ((p.factorial : ℂ)*(q.factorial : ℂ)*(L.factorial : ℂ)) =
      -(mixedCommonWeight H d n p q L *
        (-1 : ℂ)^(2*d-(L : ℤ)-m-r-2)) := by
  have phase : m+n+r+2-(p : ℤ)-(H : ℤ)-d+(q : ℤ)+(L : ℤ) =
      (n+1-(p : ℤ)-(H : ℤ)+(q : ℤ)+d +
        (2*d-(L : ℤ)-m-r-2)+1)+2*(m+r+1-2*d+(L : ℤ)) := by ring
  rw [phase, phase_even_shift, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
    zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  simp only [mixedCommonWeight, zpow_one]
  ring

private theorem second_input_common_phase (H : ℕ) (d n r : ℤ)
    (p q j ell h : ℕ) :
    (-1 : ℂ)^r * (-1 : ℂ)^j *
      (-1 : ℂ)^(n+r-(j : ℤ)+1-(p : ℤ)-(H : ℤ)+(q : ℤ)+d-
        2*(ell : ℤ)-(h : ℤ)) =
      (-1 : ℂ)^(n+1-(p : ℤ)-(H : ℤ)+(q : ℤ)+d) * (-1 : ℂ)^h := by
  rw [← zpow_natCast, ← zpow_natCast,
    ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
    ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
    ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  convert phase_even_shift
    (n+1-(p : ℤ)-(H : ℤ)+(q : ℤ)+d+(h : ℤ))
    (r-(ell : ℤ)-(h : ℤ)) using 1 <;> congr 1 <;> ring

private theorem cube_sum_rotate (N : ℕ) (f : ℕ → ℕ → ℕ → ℂ) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, f i j k) =
      ∑ k ∈ Finset.range N, ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, f i j k := by
  calc
    _ = ∑ i ∈ Finset.range N, ∑ k ∈ Finset.range N,
        ∑ j ∈ Finset.range N, f i j k := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

private theorem mixed_second_input_branch_contracted (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H K : ℕ) (d m n r E : ℤ)
    (a : fixedGrade D d) (b : fixedGrade D E)
    (hE : E = (H : ℤ)+(K : ℤ)+d-m-n-r-2) (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (N : ℕ) (hN : ((K : ℤ)+d-m-2).toNat ≤ N)
    (hS : sourceLoweringCutoff D a.val ≤ N) :
    (-1 : ℂ)^r * (∑ᶠ j : ℕ, ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) *
      normalizedCoefficient D hu (n+r-(j : ℤ)) u
        (((fixedParitySlice D hu (-1)
          (⟨a.val,a.property.2⟩ : FixedCarrier D))[[m+(j : ℤ)]]) v) E b) =
    ∑ q ∈ Finset.range (H-1), ∑ p ∈ Finset.range N, ∑ L ∈ Finset.range N,
      mixedCommonWeight H d n p q L *
        (∑ k ∈ Finset.range N,
          ((-1 : ℂ)^k * Ring.choose ((2*d-(L : ℤ)-m-r-2 : ℤ) : ℂ) k) *
            mixedSourceFirst D hu H d m n r a.val b.val u.val v.val p q L k) := by
  classical
  have finite : (∑ᶠ j : ℕ, ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) *
      normalizedCoefficient D hu (n+r-(j : ℤ)) u
        (((fixedParitySlice D hu (-1)
          (⟨a.val,a.property.2⟩ : FixedCarrier D))[[m+(j : ℤ)]]) v) E b) =
      ∑ j ∈ Finset.range N, ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) *
        normalizedCoefficient D hu (n+r-(j : ℤ)) u
          (((fixedParitySlice D hu (-1)
            (⟨a.val,a.property.2⟩ : FixedCarrier D))[[m+(j : ℤ)]]) v) E b := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra outside
    have energy := original_mode_integer_energy D hu d (K : ℤ) (m+(j : ℤ))
      a.val a.property.1 v.val hvK
    have zero := integer_energy_zero D hu h24 ((K : ℤ)+d-(m+(j : ℤ))-1)
      _ energy (by have := Finset.mem_range.not.mp outside; omega)
    have input : ((fixedParitySlice D hu (-1)
        (⟨a.val,a.property.2⟩ : FixedCarrier D))[[m+(j : ℤ)]]) v = 0 := by
      apply Subtype.ext
      change (correctedField D hu a.val).coeff (2*(-(m+(j : ℤ))-1)) v.val = 0
      rw [show 2*(-(m+(j : ℤ))-1) = -2*(m+(j : ℤ))-2 by ring]
      exact zero
    apply hj
    simp only [input, map_zero, DirectSum.zero_apply, LinearMap.zero_apply, mul_zero]
  rw [finite]
  simp_rw [mixed_second_input_reindexed_pairing D hu h24 H K d m n r E a b hE
    u v huH hvK (N := N) (hN := hN)]
  let c (p q : ℕ) : ℂ :=
    (-1 : ℂ)^(n+1-(p : ℤ)-(H : ℤ)+(q : ℤ)+d) /
      ((p.factorial : ℂ)*(q.factorial : ℂ))
  let F (p q j h ell z : ℕ) : ℂ :=
    ((ell.factorial : ℂ)⁻¹*(z.factorial : ℂ)⁻¹) *
      (Ring.choose (2*(d : ℂ)-(m : ℂ)-2-(j : ℂ)-(ell : ℂ)) h *
        mixedSourceFirst D hu H d m n r a.val b.val u.val v.val p q
          (ell+z) (j+ell+h))
  have sourceSum (p q j ell h : ℕ) :
      (∑ᶠ z : ℕ,
        (((-1 : ℂ)^(n+r-(j : ℤ)+1-(p : ℤ)-(H : ℤ)+(q : ℤ)+d-
            2*(ell : ℤ)-(h : ℤ)))/
          ((p.factorial : ℂ)*(q.factorial : ℂ)*(ell.factorial : ℂ)*(z.factorial : ℂ))) *
        Ring.choose (2*(d : ℂ)-(m : ℂ)-2-(j : ℂ)-(ell : ℂ)) h *
        mixedSourceFirst D hu H d m n r a.val b.val u.val v.val p q
          (ell+z) (j+ell+h)) =
      ∑ z ∈ Finset.range N,
        (((-1 : ℂ)^(n+r-(j : ℤ)+1-(p : ℤ)-(H : ℤ)+(q : ℤ)+d-
            2*(ell : ℤ)-(h : ℤ)))/
          ((p.factorial : ℂ)*(q.factorial : ℂ)*(ell.factorial : ℂ)*(z.factorial : ℂ))) *
        Ring.choose (2*(d : ℂ)-(m : ℂ)-2-(j : ℂ)-(ell : ℂ)) h *
        mixedSourceFirst D hu H d m n r a.val b.val u.val v.val p q
          (ell+z) (j+ell+h) := by
    apply finsum_eq_sum_of_support_subset
    intro z hz
    by_contra outside
    have killed := source_lowering_zero D hu a.val (ell+z)
      (by have := Finset.mem_range.not.mp outside; omega)
    apply hz
    simp only [mixedSourceFirst, killed, map_zero, Pi.zero_apply,
      LinearMap.zero_apply, mul_zero]
  change (-1 : ℂ)^r * (∑ j ∈ Finset.range N,
    ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) *
    (∑ q ∈ Finset.range (H-1), ∑ p ∈ Finset.range N,
      ∑ ell ∈ Finset.range N, ∑ h ∈ Finset.range N, _)) = _
  dsimp only [mixedSourceFirst] at sourceSum
  simp_rw [sourceSum]
  calc
    _ = ∑ q ∈ Finset.range (H-1), ∑ p ∈ Finset.range N,
        c p q * (∑ j ∈ Finset.range N, ∑ h ∈ Finset.range N,
          (Ring.choose (r : ℂ) j * (-1 : ℂ)^h) *
            (∑ ell ∈ Finset.range N, ∑ z ∈ Finset.range N, F p q j h ell z)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro ell hell
      apply Finset.sum_congr rfl
      intro z hz
      have phase := second_input_common_phase H d n r p q j ell h
      dsimp only [c, F]
      simp only [div_eq_mul_inv, mul_inv_rev]
      linear_combination (norm := (dsimp only [mixedSourceFirst]; ring))
        ((p.factorial : ℂ)⁻¹*(q.factorial : ℂ)⁻¹*
          (ell.factorial : ℂ)⁻¹*(z.factorial : ℂ)⁻¹*
          Ring.choose (r : ℂ) j *
          Ring.choose (2*(d : ℂ)-(m : ℂ)-2-(j : ℂ)-(ell : ℂ)) h *
          mixedSourceFirst D hu H d m n r a.val b.val u.val v.val p q
            (ell+z) (j+ell+h)) * phase
    _ = ∑ q ∈ Finset.range (H-1), ∑ p ∈ Finset.range N,
        c p q * (∑ j ∈ Finset.range N, ∑ h ∈ Finset.range N,
          (Ring.choose (r : ℂ) j * (-1 : ℂ)^h) *
            (∑ L ∈ Finset.range N, (L.factorial : ℂ)⁻¹ *
              (∑ ell ∈ Finset.range N, Ring.choose (L : ℂ) ell *
                Ring.choose (2*(d : ℂ)-(m : ℂ)-2-(j : ℂ)-(ell : ℂ)) h *
                mixedSourceFirst D hu H d m n r a.val b.val u.val v.val p q L
                  (j+ell+h)))) := by
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro p hp
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro h hh
      congr 1
      exact mixed_second_source_factorial_contraction D hu H d m n r a.val b.val
        u.val v.val p q j h N hS
    _ = ∑ q ∈ Finset.range (H-1), ∑ p ∈ Finset.range N, ∑ L ∈ Finset.range N,
        mixedCommonWeight H d n p q L *
          (∑ ell ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ h ∈ Finset.range N,
            Ring.choose (L : ℂ) ell * Ring.choose (r : ℂ) j * (-1 : ℂ)^h *
            Ring.choose (2*(d : ℂ)-(m : ℂ)-2-(j : ℂ)-(ell : ℂ)) h *
            mixedSourceFirst D hu H d m n r a.val b.val u.val v.val p q L
              (j+ell+h)) := by
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro p hp
      simp_rw [Finset.mul_sum]
      rw [cube_sum_rotate]
      apply Finset.sum_congr rfl
      intro L hL
      rw [cube_sum_rotate]
      apply Finset.sum_congr rfl
      intro ell hell
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro h hh
      dsimp only [mixedCommonWeight, c]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro L hL
      rw [mixed_second_contraction D hu h24 H K d m n r E a.val b.val
        b.property.1 hE u.val v.val huH p q L N hN]

private theorem lowering_integer_zero_after (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H : ℕ) (u : ActualTensor D hu)
    (huH : actualTensorL0 D hu u = (H : ℂ) • u) (q : ℕ) (hq : H-1 ≤ q) :
    (T D hu ^ q) u = 0 := by
  exact integer_energy_zero D hu h24 ((H : ℤ)-(q : ℤ)) _
    (lowering_integer_energy D hu h24 (H : ℤ) u huH q) (by omega)

private def mixedFirstSum (D : LatticeData) (hu : IsUnit D.G.det)
    (H : ℕ) (d m n r : ℤ) (a b : Carrier D) (u v : ActualTensor D hu)
    (N p q L : ℕ) : ℂ :=
  ∑ k ∈ Finset.range N,
    ((-1 : ℂ)^k * Ring.choose ((2*d-(L : ℤ)-m-r-2 : ℤ) : ℂ) k) *
      mixedSourceFirst D hu H d m n r a b u v p q L k

private def mixedSecondSum (D : LatticeData) (hu : IsUnit D.G.det)
    (H : ℕ) (d m n r : ℤ) (a b : Carrier D) (u v : ActualTensor D hu)
    (N p q L : ℕ) : ℂ :=
  ∑ k ∈ Finset.range N,
    ((-1 : ℂ)^k * Ring.choose ((2*d-(L : ℤ)-m-r-2 : ℤ) : ℂ) k) *
      mixedSourceSecond D hu H d m n r a b u v p q L k

private def mixedIterate (D : LatticeData) (hu : IsUnit D.G.det)
    (H : ℕ) (d m n r : ℤ) (a b : Carrier D) (u v : ActualTensor D hu)
    (p q L : ℕ) : ℂ :=
  ∑ᶠ j : ℕ, Ring.choose (r : ℂ) j *
    actualForm D hu ((T D hu ^ p) v)
      ((correctedField D hu
        (((Y D ((originalL1 D ^ L) a))[[2*d-(L : ℤ)-m-r-2+(j : ℤ)]]) b)).coeff
        (-2*(r+(2*(H : ℤ)-n-r-2+(p : ℤ)-(q : ℤ))-(j : ℤ))-2)
        ((T D hu ^ q) u))

private theorem mixed_first_input_common_cube (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H K : ℕ) (d m n r E : ℤ)
    (a : fixedGrade D d) (b : fixedGrade D E) (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (N : ℕ) (hN : ((H : ℤ)+d-r-2).toNat ≤ N) (hK : K-1 ≤ N) :
    (∑ᶠ j : ℕ, Ring.choose (m : ℂ) j *
      (normalizedCoefficient D hu (m+n-(j : ℤ))
        (((fixedParitySlice D hu (-1)
          (⟨a.val,a.property.2⟩ : FixedCarrier D))[[r+(j : ℤ)]]) u) v) E b) =
    ∑ p ∈ Finset.range N, ∑ q ∈ Finset.range N, ∑ L ∈ Finset.range N,
      mixedCommonWeight H d n p q L *
        (-(-1 : ℂ)^(2*d-(L : ℤ)-m-r-2)) *
        mixedSecondSum D hu H d m n r a.val b.val u.val v.val N p q L := by
  classical
  rw [mixed_first_input_branch_reindexed D hu h24 H K d m n r E a b u v huH hvK N hN]
  calc
    _ = ∑ p ∈ Finset.range (K-1), ∑ q ∈ Finset.range N, ∑ L ∈ Finset.range N,
        mixedCommonWeight H d n p q L *
          (-(-1 : ℂ)^(2*d-(L : ℤ)-m-r-2)) *
          mixedSecondSum D hu H d m n r a.val b.val u.val v.val N p q L := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro L hL
      rw [first_input_common_phase]
      dsimp only [mixedSecondSum, mixedSourceSecond]
      ring
    _ = _ := by
      apply Finset.sum_subset (Finset.range_mono hK)
      intro p hp outside
      have zero := lowering_integer_zero_after D hu h24 K v.val hvK p
        (by simpa using outside)
      apply Finset.sum_eq_zero
      intro q hq
      apply Finset.sum_eq_zero
      intro L hL
      simp only [mixedSecondSum, mixedSourceSecond, zero, map_zero,
        LinearMap.zero_apply, mul_zero, Finset.sum_const_zero]

private theorem mixed_second_input_common_cube (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H K : ℕ) (d m n r E : ℤ)
    (a : fixedGrade D d) (b : fixedGrade D E)
    (hE : E = (H : ℤ)+(K : ℤ)+d-m-n-r-2) (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (N : ℕ) (hN : ((K : ℤ)+d-m-2).toNat ≤ N)
    (hS : sourceLoweringCutoff D a.val ≤ N) (hH : H-1 ≤ N) :
    (-1 : ℂ)^r * (∑ᶠ j : ℕ, ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) *
      normalizedCoefficient D hu (n+r-(j : ℤ)) u
        (((fixedParitySlice D hu (-1)
          (⟨a.val,a.property.2⟩ : FixedCarrier D))[[m+(j : ℤ)]]) v) E b) =
    ∑ p ∈ Finset.range N, ∑ q ∈ Finset.range N, ∑ L ∈ Finset.range N,
      mixedCommonWeight H d n p q L *
        mixedFirstSum D hu H d m n r a.val b.val u.val v.val N p q L := by
  classical
  rw [mixed_second_input_branch_contracted D hu h24 H K d m n r E a b hE
    u v huH hvK N hN hS]
  change (∑ q ∈ Finset.range (H-1), ∑ p ∈ Finset.range N, ∑ L ∈ Finset.range N,
    mixedCommonWeight H d n p q L *
      mixedFirstSum D hu H d m n r a.val b.val u.val v.val N p q L) = _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_subset (Finset.range_mono hH)
  intro q hq outside
  have zero := lowering_integer_zero_after D hu h24 H u.val huH q
    (by simpa using outside)
  apply Finset.sum_eq_zero
  intro L hL
  simp only [mixedFirstSum, mixedSourceFirst, zero, map_zero,
    mul_zero, Finset.sum_const_zero]

private theorem mixed_iterate_cancellation (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H K : ℕ) (d m n r E : ℤ)
    (a : fixedGrade D d) (b : fixedGrade D E)
    (hE : E = (H : ℤ)+(K : ℤ)+d-m-n-r-2)
    (u v : ActualTensor D hu) (huH : actualTensorL0 D hu u = (H : ℂ) • u)
    (p q L N : ℕ)
    (hNfirst : ((H : ℤ)+d-r-2).toNat ≤ N)
    (hNsecond : ((K : ℤ)+d-m-2).toNat ≤ N) :
    mixedIterate D hu H d m n r a.val b.val u v p q L =
      mixedFirstSum D hu H d m n r a.val b.val u v N p q L -
        (-1 : ℂ)^(2*d-(L : ℤ)-m-r-2) *
          mixedSecondSum D hu H d m n r a.val b.val u v N p q L := by
  have law := mixed_source_finite_cancellation D hu h24 H K d m n r E
    a b hE u v huH p q L N hNfirst hNsecond
  dsimp only at law
  have first := mixed_second_contraction D hu h24 H K d m n r E a.val b.val b.property.1
    hE u v huH p q L N hNsecond
  have second := mixed_first_contraction D hu h24 H d m n r a.val b.val a.property.1
    u v huH p q L N hNfirst
  dsimp only [mixedSourceFirst, mixedSourceSecond] at first second
  rw [first, second] at law
  exact law

private theorem original_negative_grade_zero (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (e : ℤ) (x : Carrier D) (hx : x ∈ grade D e) (he : e < 0) : x = 0 := by
  apply (carrierCoeffEquiv D).injective
  ext i
  have nonneg : 0 ≤ energy D i := by
    have hc := chargeEnergy_nonneg D hD i.1
    change 0 ≤ chargeEnergy D i.1 + (oscillatorEnergy i.2 : ℤ)
    omega
  exact (mem_grade_iff D e x).mp hx i (by omega)

private theorem mixed_iterate_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (H K : ℕ) (d m n r E : ℤ) (a : fixedGrade D d) (b : fixedGrade D E)
    (hE : E = (H : ℤ)+(K : ℤ)+d-m-n-r-2)
    (u v : ActualTensor D hu) (p q L : ℕ) :
    mixedIterate D hu H d m n r a.val b.val u v p q L =
      ∑ j ∈ Finset.range (((H : ℤ)+(K : ℤ)-n).toNat+1),
        Ring.choose (r : ℂ) j * actualForm D hu ((T D hu ^ p) v)
          ((correctedField D hu
            (((Y D ((originalL1 D ^ L) a.val))[[2*d-(L : ℤ)-m-r-2+(j : ℤ)]])
              b.val)).coeff
            (-2*(r+(2*(H : ℤ)-n-r-2+(p : ℤ)-(q : ℤ))-(j : ℤ))-2)
            ((T D hu ^ q) u)) := by
  classical
  apply finsum_eq_sum_of_support_subset
  intro j hj
  by_contra outside
  have grade := positive_actual_mode_grade D hD (d-(L : ℤ)) E
    (2*d-(L : ℤ)-m-r-2+(j : ℤ)) ((originalL1 D ^ L) a.val) b.val
    (original_l1_grade D hu d a.val a.property.1 L) b.property.1
  have zero := original_negative_grade_zero D hD _ _ grade
    (by have := Finset.mem_range.not.mp outside; omega)
  apply hj
  simp only [zero, map_zero, Pi.zero_apply, LinearMap.zero_apply, mul_zero]

private theorem four_sum_reorder (I J K L : Finset ℕ) (f : ℕ → ℕ → ℕ → ℕ → ℂ) :
    (∑ i ∈ I, ∑ j ∈ J, ∑ k ∈ K, ∑ l ∈ L, f i j k l) =
      ∑ k ∈ K, ∑ l ∈ L, ∑ j ∈ J, ∑ i ∈ I, f i j k l := by
  calc
    _ = ∑ i ∈ I, ∑ k ∈ K, ∑ j ∈ J, ∑ l ∈ L, f i j k l := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ k ∈ K, ∑ i ∈ I, ∑ j ∈ J, ∑ l ∈ L, f i j k l := Finset.sum_comm
    _ = ∑ k ∈ K, ∑ i ∈ I, ∑ l ∈ L, ∑ j ∈ J, f i j k l := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ k ∈ K, ∑ l ∈ L, ∑ i ∈ I, ∑ j ∈ J, f i j k l := by
      apply Finset.sum_congr rfl
      intro k hk
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      exact Finset.sum_comm

private theorem mixed_first_dual_common_cube (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K : ℕ) (d m n r E : ℤ) (a : fixedGrade D d) (b : fixedGrade D E)
    (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (hE : E = (H : ℤ)+(K : ℤ)+d-m-n-r-2)
    (N : ℕ) (hK : K-1 ≤ N) (hH : H-1 ≤ N)
    (hS : sourceLoweringCutoff D a.val ≤ N) :
    (∑ᶠ j : ℕ, (((-1 : ℂ)^j)*Ring.choose (r : ℂ) j) •
      oppositeAction D hu hD (m+r-(j : ℤ))
        (⟨a.val,a.property.2⟩ : FixedCarrier D)
        (normalizedCoefficient D hu (n+(j : ℤ)) u v)) E b =
    ∑ p ∈ Finset.range N, ∑ q ∈ Finset.range N, ∑ L ∈ Finset.range N,
      mixedCommonWeight H d n p q L *
        mixedIterate D hu H d m n r a.val b.val u.val v.val p q L := by
  classical
  rw [mixed_first_branch_pairing D hu hD h24 H K d m n r E a u v huH hvK hE b]
  let S := sourceLoweringCutoff D a.val
  let J := ((H : ℤ)+(K : ℤ)-n).toNat+1
  let f (p q L : ℕ) : ℂ := mixedCommonWeight H d n p q L *
    mixedIterate D hu H d m n r a.val b.val u.val v.val p q L
  have pZero (p q L : ℕ) (hp : K-1 ≤ p) : f p q L = 0 := by
    have zero := lowering_integer_zero_after D hu h24 K v.val hvK p hp
    simp only [f, mixedIterate, zero, map_zero, LinearMap.zero_apply, mul_zero,
      finsum_zero]
  have qZero (p q L : ℕ) (hq : H-1 ≤ q) : f p q L = 0 := by
    have zero := lowering_integer_zero_after D hu h24 H u.val huH q hq
    simp only [f, mixedIterate, zero, map_zero, mul_zero, finsum_zero]
  have LZero (p q L : ℕ) (hL : S ≤ L) : f p q L = 0 := by
    have zero := source_lowering_zero D hu a.val L hL
    simp only [f, mixedIterate, zero, map_zero, Pi.zero_apply, LinearMap.zero_apply,
      mul_zero, finsum_zero]
  calc
    _ = ∑ p ∈ Finset.range (K-1), ∑ q ∈ Finset.range (H-1),
        ∑ L ∈ Finset.range S, f p q L := by
      simp_rw [Finset.mul_sum]
      rw [four_sum_reorder]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro L hL
      dsimp only [f]
      rw [mixed_iterate_finite D hu hD H K d m n r E a b hE u.val v.val p q L,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have mode : 2*d-(L : ℤ)-m-r+(j : ℤ)-2 =
          2*d-(L : ℤ)-m-r-2+(j : ℤ) := by ring
      have exponent : 2*(n+(j : ℤ)+1-(p : ℤ)-2*(H : ℤ)+(q : ℤ)) =
          -2*(r+(2*(H : ℤ)-n-r-2+(p : ℤ)-(q : ℤ))-(j : ℤ))-2 := by ring
      have phase : (-1 : ℂ)^j * (-1 : ℂ)^d *
          (-1 : ℂ)^((H : ℤ)+(n+(j : ℤ)+1-(p : ℤ)-2*(H : ℤ)+(q : ℤ))) =
          (-1 : ℂ)^(n+1-(p : ℤ)-(H : ℤ)+(q : ℤ)+d) := by
        rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
          ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
        convert phase_even_shift (n+1-(p : ℤ)-(H : ℤ)+(q : ℤ)+d) (j : ℤ)
          using 1 <;> congr 1 <;> ring
      rw [mode, exponent]
      dsimp only [mixedCommonWeight]
      simp only [div_eq_mul_inv, mul_inv_rev]
      linear_combination
        ((p.factorial : ℂ)⁻¹*(q.factorial : ℂ)⁻¹*(L.factorial : ℂ)⁻¹*
          Ring.choose (r : ℂ) j * actualForm D hu ((T D hu ^ p) v.val)
            ((correctedField D hu
              (((Y D ((originalL1 D ^ L) a.val))[[2*d-(L : ℤ)-m-r-2+(j : ℤ)]])
                b.val)).coeff
              (-2*(r+(2*(H : ℤ)-n-r-2+(p : ℤ)-(q : ℤ))-(j : ℤ))-2)
              ((T D hu ^ q) u.val))) * phase
    _ = ∑ p ∈ Finset.range N, ∑ q ∈ Finset.range (H-1),
        ∑ L ∈ Finset.range S, f p q L := by
      apply Finset.sum_subset (Finset.range_mono hK)
      intro p hp outside
      apply Finset.sum_eq_zero
      intro q hq
      apply Finset.sum_eq_zero
      intro L hL
      exact pZero p q L (by simpa using outside)
    _ = ∑ p ∈ Finset.range N, ∑ q ∈ Finset.range N,
        ∑ L ∈ Finset.range S, f p q L := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_subset (Finset.range_mono hH)
      intro q hq outside
      apply Finset.sum_eq_zero
      intro L hL
      exact qZero p q L (by simpa using outside)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_subset (Finset.range_mono hS)
      intro L hL outside
      exact LZero p q L (by simpa using outside)

/-- Both actual signed input branches and the dual action agree on the full target grade. -/
theorem mixed_homogeneous_grade_pairing (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K : ℕ) (d m n r E : ℤ) (a : fixedGrade D d) (b : fixedGrade D E)
    (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (hE : E = (H : ℤ)+(K : ℤ)+d-m-n-r-2) :
    (∑ᶠ j : ℕ, Ring.choose (m : ℂ) j *
      normalizedCoefficient D hu (m+n-(j : ℤ))
        (((fixedParitySlice D hu (-1)
          (⟨a.val,a.property.2⟩ : FixedCarrier D))[[r+(j : ℤ)]]) u) v E b) =
    (∑ᶠ j : ℕ, (((-1 : ℂ)^j)*Ring.choose (r : ℂ) j) •
      oppositeAction D hu hD (m+r-(j : ℤ))
        (⟨a.val,a.property.2⟩ : FixedCarrier D)
        (normalizedCoefficient D hu (n+(j : ℤ)) u v)) E b -
    (-1 : ℂ)^r * (∑ᶠ j : ℕ, ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) *
      normalizedCoefficient D hu (n+r-(j : ℤ)) u
        (((fixedParitySlice D hu (-1)
          (⟨a.val,a.property.2⟩ : FixedCarrier D))[[m+(j : ℤ)]]) v) E b) := by
  classical
  let N := (H-1)+(K-1)+sourceLoweringCutoff D a.val+
    ((H : ℤ)+d-r-2).toNat+((K : ℤ)+d-m-2).toNat
  have hNfirst : ((H : ℤ)+d-r-2).toNat ≤ N := by dsimp [N]; omega
  have hNsecond : ((K : ℤ)+d-m-2).toNat ≤ N := by dsimp [N]; omega
  have hH : H-1 ≤ N := by dsimp [N]; omega
  have hK : K-1 ≤ N := by dsimp [N]; omega
  have hS : sourceLoweringCutoff D a.val ≤ N := by dsimp [N]; omega
  rw [mixed_first_input_common_cube D hu h24 H K d m n r E a b u v huH hvK N hNfirst hK,
    mixed_first_dual_common_cube D hu hD h24 H K d m n r E a b u v huH hvK hE
      N hK hH hS,
    mixed_second_input_common_cube D hu h24 H K d m n r E a b hE u v huH hvK
      N hNsecond hS hH]
  simp_rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro L hL
  rw [mixed_iterate_cancellation D hu h24 H K d m n r E a b hE u.val v.val huH
    p q L N hNfirst hNsecond]
  ring

end D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
