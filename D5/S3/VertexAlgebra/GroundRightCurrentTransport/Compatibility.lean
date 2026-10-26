/- GID: D5/S3/VertexAlgebra/GroundRightCurrentTransport/Compatibility
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/GroundRightCurrentTransport/Compatibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Supported inverse-residue recovery of all signed compatibility coefficients. -/
import D5.S3.VertexAlgebra.GroundRightCurrentTransport.Interchange

/-! The finite Pascal propagation follows the native CurrentBorcherds proof;
    here the first field and source iterate are independent arbitrary fields. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
open scoped BigOperators VertexOperator
namespace D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus
universe u
variable {M : Type u} [AddCommGroup M] [Module ℂ M]

local macro "ext_modes" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.ext_modes))
local macro "R_mode" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.R_mode))
local macro "Z_mode" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.Z_mode))
local macro "Q_pad" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Interchange 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.Q_pad))
local macro "finiteConvolution" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds.finite_convolution))
local macro "high" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.high))
local macro "upper" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.upper))

/-- The source and the two ordered target sequences remain separate. -/
def leftTerm (U : ℤ → VertexOperator ℂ M) (s p q r : ℤ) (x : M) (j : ℕ) : M :=
  Ring.choose ((p : ℂ)+(s : ℂ)/2) j • ((U (r+j))[[p+q-j]]) x

def firstTerm (A B : VertexOperator ℂ M) (p q r : ℤ) (x : M) (j : ℕ) : M :=
  residueWeight r j • (A[[p+r-j]]) ((B[[q+j]]) x)

def secondTerm (A B : VertexOperator ℂ M) (p q r : ℤ) (x : M) (j : ℕ) : M :=
  residueWeight r j • ((-1 : ℂ)^r • (B[[q+r-j]]) ((A[[p+j]]) x))

def fullLaw (A B : VertexOperator ℂ M) (U : ℤ → VertexOperator ℂ M) (s : ℤ) : Prop :=
  ∀ p q r : ℤ, ∀ x : M,
    Function.HasFiniteSupport (leftTerm U s p q r x) ∧
    Function.HasFiniteSupport (firstTerm A B p q r x) ∧
    Function.HasFiniteSupport (secondTerm A B p q r x) ∧
    (∑ᶠ j : ℕ, leftTerm U s p q r x j) =
      (∑ᶠ j : ℕ, firstTerm A B p q r x j) -
      (∑ᶠ j : ℕ, secondTerm A B p q r x j)

private theorem sequence_supports (A B : VertexOperator ℂ M)
    (U : ℤ → VertexOperator ℂ M) (p q r : ℤ) (x : M)
    (KU : ℕ) (tail : ∀ t : ℤ, (KU : ℤ) ≤ t → U t = 0) :
    Function.HasFiniteSupport (fun j : ℕ => ((U (r+j))[[p+q-j]]) x) ∧
    Function.HasFiniteSupport (fun j : ℕ => (A[[p+r-j]]) ((B[[q+j]]) x)) ∧
    Function.HasFiniteSupport (fun j : ℕ => (B[[q+r-j]]) ((A[[p+j]]) x)) := by
  classical
  constructor
  · refine (Finset.range ((KU : ℤ)-r).toNat).finite_toSet.subset ?_
    intro j hj
    by_contra outside
    have hz := tail (r+j) (by have := Finset.mem_range.not.mp outside; omega)
    exact hj (by simp [hz])
  constructor
  · refine (Finset.range ((upper B x : ℤ)-q).toNat).finite_toSet.subset ?_
    intro j hj
    by_contra outside
    have hz := high B x (q+j) (by have := Finset.mem_range.not.mp outside; omega)
    exact hj (by simp [hz])
  · refine (Finset.range ((upper A x : ℤ)-p).toNat).finite_toSet.subset ?_
    intro j hj
    by_contra outside
    have hz := high A x (p+j) (by have := Finset.mem_range.not.mp outside; omega)
    exact hj (by simp [hz])

/-- Two finite triangular transforms cancel before the original source is used. -/
private theorem zero_seed (A B : VertexOperator ℂ M)
    (U : ℤ → VertexOperator ℂ M) (s q r : ℤ) (x : M)
    (KU KR : ℕ) (tail : ∀ t : ℤ, (KU : ℤ) ≤ t → U t = 0)
    (valid : Valid A B KR) (inverse : ∀ t, U t = Q A B s t KR) :
    (∑ᶠ j : ℕ, leftTerm U s 0 q r x j) = (((R A B r)[[q]])) x := by
  classical
  let K := ((max KU KR : ℕ) : ℤ) - r
  let N := K.toNat + 1
  have boundU : (KU : ℤ) ≤ r+N := by dsimp [N, K]; omega
  have boundR : (KR : ℤ) ≤ r+N := by dsimp [N, K]; omega
  let v (j : ℕ) := (((R A B (r+j))[[q-j]])) x
  have vt (j : ℕ) (hj : N ≤ j) : v j = 0 := by
    simp [v, valid (r+j) (by omega)]
  have leftFinite : (∑ᶠ j : ℕ, leftTerm U s 0 q r x j) =
      ∑ j ∈ Finset.range N, Ring.choose ((s : ℂ)/2) j • ((U (r+j))[[q-j]]) x := by
    simp only [leftTerm, Int.cast_zero, zero_add]
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra outside
    have hz := tail (r+j) (by have := Finset.mem_range.not.mp outside; omega)
    exact hj (by simp [hz])
  have row (j : ℕ) : ((U (r+j))[[q-j]]) x =
      ∑ k ∈ Finset.range N, Ring.choose (-(s : ℂ)/2) k • v (j+k) := by
    rw [inverse, Q_pad A B s (r+j) KR N valid (by omega)]
    simp only [map_sum, Finset.sum_apply, LinearMap.sum_apply, map_smul,
      Pi.smul_apply, LinearMap.smul_apply, Z_mode]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [v, Nat.cast_add, add_assoc, sub_sub]
  rw [leftFinite]
  simp_rw [row]
  rw [finiteConvolution ((s : ℂ)/2) (-(s : ℂ)/2) N v vt,
    show (s : ℂ)/2 + -(s : ℂ)/2 = 0 by ring]
  rw [Finset.sum_eq_single 0]
  · simp [v]
  · intro j hj hne
    rcases j with _ | j
    · exact (hne rfl).elim
    · simp
  · simp [N]

private def discrepancy (A B : VertexOperator ℂ M)
    (U : ℤ → VertexOperator ℂ M) (s p q r : ℤ) (x : M) : M :=
  (∑ᶠ j : ℕ, leftTerm U s p q r x j) -
  (∑ᶠ j : ℕ, firstTerm A B p q r x j) +
  (∑ᶠ j : ℕ, secondTerm A B p q r x j)

set_option maxHeartbeats 4000000 in
-- The supported Pascal recurrence retains three independently finite sequences.
private theorem discrepancy_recurrence (A B : VertexOperator ℂ M)
    (U : ℤ → VertexOperator ℂ M) (s p q r : ℤ) (x : M)
    (KU : ℕ) (tail : ∀ t : ℤ, (KU : ℤ) ≤ t → U t = 0) :
    discrepancy A B U s (p+1) q r x =
      discrepancy A B U s p (q+1) r x + discrepancy A B U s p q (r+1) x := by
  classical
  let weight (parameter : ℤ) (offset : ℕ) :=
    (-1 : ℂ) ^ offset * Ring.choose (parameter : ℂ) offset
  let zeroSucc : Option ℕ ≃ ℕ := {
    toFun value := match value with | none => 0 | some offset => offset + 1
    invFun value := match value with | 0 => none | offset + 1 => some offset
    left_inv value := by cases value <;> rfl
    right_inv value := by cases value <;> rfl }
  have splitSum (term : ℕ → M) (finite : Function.HasFiniteSupport term) : ∑ᶠ offset : ℕ, term offset = term 0 + ∑ᶠ offset : ℕ, term (offset + 1) := by
    rw [← finsum_comp_equiv zeroSucc, finsum_option]
    · rfl
    · exact finite.fun_comp_of_injective (g := fun offset : ℕ => offset + 1) (fun first second equality => Nat.add_right_cancel equality)
  have pascal (parameter : ℂ) (offset : ℕ) :
      Ring.choose (parameter + 1) (offset + 1) =
        Ring.choose parameter offset + Ring.choose parameter (offset + 1) :=
    Ring.choose_succ_succ parameter offset
  have weightedPascal (parameter : ℤ) (offset : ℕ) : weight (parameter + 1) (offset + 1) = weight parameter (offset + 1) - weight parameter offset := by
    dsimp only [weight]; rw [Int.cast_add, Int.cast_one, pascal, pow_succ]; ring
  have chooseZero (parameter : ℂ) : Ring.choose parameter 0 = 1 := by simp
  have weightZero (parameter : ℤ) : weight parameter 0 = 1 := by simp [weight, chooseZero]
  have sumPascal (parameter : ℂ) (sequence : ℕ → M) (finite : Function.HasFiniteSupport sequence) : (∑ᶠ offset : ℕ, Ring.choose (parameter + 1) offset • sequence offset) =
    (∑ᶠ offset : ℕ, Ring.choose parameter offset • sequence offset) + (∑ᶠ offset : ℕ, Ring.choose parameter offset • sequence (offset + 1)) := by
    have tailFinite := finite.fun_comp_of_injective (g := fun offset : ℕ => offset + 1) (fun first second equality => Nat.add_right_cancel equality)
    have nextFinite : Function.HasFiniteSupport (fun offset : ℕ =>
        Ring.choose (parameter + 1) offset • sequence offset) :=
      finite.smul_right (Ring.choose (parameter + 1))
    have currentFinite : Function.HasFiniteSupport (fun offset : ℕ =>
        Ring.choose parameter offset • sequence offset) :=
      finite.smul_right (Ring.choose parameter)
    rw [splitSum _ nextFinite, splitSum _ currentFinite]; simp only [chooseZero, one_smul]; simp_rw [pascal, add_smul]
    have firstTail : Function.HasFiniteSupport (fun offset : ℕ =>
        Ring.choose parameter offset • sequence (offset + 1)) :=
      tailFinite.smul_right (Ring.choose parameter)
    have secondTail : Function.HasFiniteSupport (fun offset : ℕ =>
        Ring.choose parameter (offset + 1) • sequence (offset + 1)) :=
      tailFinite.smul_right (fun offset => Ring.choose parameter (offset + 1))
    rw [finsum_add_distrib firstTail secondTail]; abel
  have sumWeightedPascal (parameter : ℤ) (sequence : ℕ → M) (finite : Function.HasFiniteSupport sequence) : (∑ᶠ offset : ℕ, weight (parameter + 1) offset • sequence offset) =
    (∑ᶠ offset : ℕ, weight parameter offset • sequence offset) - (∑ᶠ offset : ℕ, weight parameter offset • sequence (offset + 1)) := by
    have tailFinite := finite.fun_comp_of_injective (g := fun offset : ℕ => offset + 1) (fun first second equality => Nat.add_right_cancel equality)
    have nextFinite : Function.HasFiniteSupport (fun offset : ℕ =>
        weight (parameter + 1) offset • sequence offset) :=
      finite.smul_right (weight (parameter + 1))
    have currentFinite : Function.HasFiniteSupport (fun offset : ℕ =>
        weight parameter offset • sequence offset) := finite.smul_right (weight parameter)
    rw [splitSum _ nextFinite, splitSum _ currentFinite]; simp only [weightZero, one_smul]; simp_rw [weightedPascal, sub_smul]
    have firstTail : Function.HasFiniteSupport (fun offset : ℕ =>
        weight parameter (offset + 1) • sequence (offset + 1)) :=
      tailFinite.smul_right (fun offset => weight parameter (offset + 1))
    have secondTail : Function.HasFiniteSupport (fun offset : ℕ =>
        weight parameter offset • sequence (offset + 1)) :=
      tailFinite.smul_right (weight parameter)
    rw [finsum_sub_distrib firstTail secondTail]; abel
  have leftLaw :
      (∑ᶠ j : ℕ, leftTerm U s (p + 1) q r x j) =
      (∑ᶠ j : ℕ, leftTerm U s p (q + 1) r x j) +
      (∑ᶠ j : ℕ, leftTerm U s p q (r + 1) x j) := by
    let sequence (j : ℕ) :=
      ((U (r+j))[[p+1+q-j]]) x
    have initial (j : ℕ) : leftTerm U s (p + 1) q r x j =
        Ring.choose (((p : ℂ) + (s : ℂ) / 2) + 1) j • sequence j := by
      dsimp only [leftTerm, sequence]
      congr 2
      push_cast
      ring
    have current (j : ℕ) : leftTerm U s p (q + 1) r x j =
        Ring.choose ((p : ℂ) + (s : ℂ) / 2) j • sequence j := by
      dsimp only [leftTerm, sequence]
      rw [show p + (q + 1) = p + 1 + q by omega]
    have shifted (j : ℕ) : leftTerm U s p q (r + 1) x j =
        Ring.choose ((p : ℂ) + (s : ℂ) / 2) j • sequence (j + 1) := by
      dsimp only [leftTerm, sequence]
      push_cast
      rw [show r + ((j : ℤ) + 1) = r + 1 + j by omega,
        show p + 1 + q - ((j : ℤ) + 1) = p + q - j by omega]
    simp_rw [initial, current, shifted]
    exact sumPascal ((p : ℂ) + (s : ℂ) / 2) sequence
      (sequence_supports A B U (p+1) q r x KU tail).1
  have firstRightLaw :
      (∑ᶠ j : ℕ, firstTerm A B (p + 1) q r x j) =
      (∑ᶠ j : ℕ, firstTerm A B p (q + 1) r x j) +
      (∑ᶠ j : ℕ, firstTerm A B p q (r + 1) x j) := by
    let sequence (j : ℕ) :=
      (A[[p+(r+1)-j]]) ((B[[q+j]]) x)
    have initial (j : ℕ) : firstTerm A B (p + 1) q r x j =
        weight r j • sequence j := by
      dsimp only [firstTerm, residueWeight, weight, sequence]
      rw [show p + 1 + r = p + (r + 1) by omega]
    have current (j : ℕ) : firstTerm A B p q (r + 1) x j =
        weight (r + 1) j • sequence j := by rfl
    have shifted (j : ℕ) : firstTerm A B p (q + 1) r x j =
        weight r j • sequence (j + 1) := by
      dsimp only [firstTerm, residueWeight, weight, sequence]
      push_cast
      rw [show p + (r + 1) - ((j : ℤ) + 1) = p + r - j by omega,
        show q + ((j : ℤ) + 1) = q + 1 + j by omega]
    simp_rw [initial, current, shifted]
    exact sub_eq_iff_eq_add'.mp (sumWeightedPascal r sequence
      (sequence_supports A B U p q (r+1) x KU tail).2.1).symm
  have sign : (-1 : ℂ) ^ (r + 1) = -((-1 : ℂ) ^ r) := by
    rw [zpow_add₀ (by norm_num)]
    norm_num
  have secondRightLaw :
      (∑ᶠ j : ℕ, secondTerm A B (p + 1) q r x j) =
      (∑ᶠ j : ℕ, secondTerm A B p (q + 1) r x j) +
      (∑ᶠ j : ℕ, secondTerm A B p q (r + 1) x j) := by
    let sequence (j : ℕ) :=
      (B[[q+(r+1)-j]]) ((A[[p+j]]) x)
    have initial (j : ℕ) : secondTerm A B p (q + 1) r x j =
        (-1 : ℂ) ^ r • (weight r j • sequence j) := by
      dsimp only [secondTerm, residueWeight, weight, sequence]
      rw [show q + 1 + r = q + (r + 1) by omega, smul_comm]
    have current (j : ℕ) : secondTerm A B p q (r + 1) x j =
        -((-1 : ℂ) ^ r) • (weight (r + 1) j • sequence j) := by
      dsimp only [secondTerm, residueWeight, weight, sequence]
      rw [sign, smul_comm]
    have shifted (j : ℕ) : secondTerm A B (p + 1) q r x j =
        (-1 : ℂ) ^ r • (weight r j • sequence (j + 1)) := by
      dsimp only [secondTerm, residueWeight, weight, sequence]
      push_cast
      rw [show q + (r + 1) - ((j : ℤ) + 1) = q + r - j by omega,
        show p + ((j : ℤ) + 1) = p + 1 + j by omega, smul_comm]
    simp_rw [initial, current, shifted, ← smul_finsum]
    rw [sumWeightedPascal r sequence (sequence_supports A B U p q (r+1) x KU tail).2.2]
    module
  unfold discrepancy
  rw [leftLaw, firstRightLaw, secondRightLaw]
  abel

private theorem ordered_residue (A B : VertexOperator ℂ M)
    (p q r : ℤ) (x : M) :
    (((R (Z (-p) A) B r)[[q]])) x =
      (∑ᶠ j : ℕ, firstTerm A B p q r x j) -
      (∑ᶠ j : ℕ, secondTerm A B p q r x j) := by
  rw [R_mode]
  simp only [Z_mode, sub_neg_eq_add]
  have first (j : ℕ) : r-(j:ℤ)+p = p+r-j := by omega
  have second (j : ℕ) : (j:ℤ)+p = p+j := by omega
  simp_rw [first, second]
  unfold firstTerm secondTerm
  congr 1
  rw [smul_finsum]
  apply finsum_congr
  intro j
  rw [smul_comm]

theorem recover_full (A B : VertexOperator ℂ M)
    (U : ℤ → VertexOperator ℂ M) (s : ℤ) (KU KR : ℕ)
    (tail : ∀ t : ℤ, (KU : ℤ) ≤ t → U t = 0)
    (locality : ∀ p : ℤ, Valid (Z (-p) A) B KR)
    (valid : Valid A B KR) (inverse : ∀ t, U t = Q A B s t KR) :
    fullLaw A B U s := by
  classical
  intro p q r x
  let cutoff := max KU KR
  let E (p q r : ℤ) := discrepancy A B U s p q r x
  have highSeed (p q r : ℤ) (hr : (cutoff : ℤ) ≤ r) : E p q r = 0 := by
    have leftZero : (∑ᶠ j : ℕ, leftTerm U s p q r x j) = 0 := by
      apply finsum_eq_zero_of_forall_eq_zero
      intro j
      simp [leftTerm, tail (r+j) (by dsimp [cutoff] at hr; omega)]
    have rightZero := congrArg (fun C : VertexOperator ℂ M => (C[[q]]) x)
      (locality p r (by dsimp [cutoff] at hr; omega))
    rw [ordered_residue] at rightZero
    change (_-_) = 0 at rightZero
    dsimp only [E, discrepancy]
    rw [leftZero, sub_eq_zero.mp rightZero]
    abel
  have zeroSeed (q r : ℤ) : E 0 q r = 0 := by
    have seed := zero_seed A B U s q r x KU KR tail valid inverse
    have ordered := ordered_residue A B 0 q r x
    have z0 : Z 0 A = A := by
      apply HVertexOperator.coeff_inj
      funext e
      simp [Z]
    simp only [neg_zero, z0] at ordered
    dsimp only [E, discrepancy]
    rw [seed, ordered]
    abel
  have recurrence (p q r : ℤ) : E (p+1) q r = E p (q+1) r + E p q (r+1) :=
    discrepancy_recurrence A B U s p q r x KU tail
  have positive (degree : ℕ) : ∀ q r : ℤ, E degree q r = 0 := by
    induction degree with
    | zero => exact zeroSeed
    | succ degree ih =>
      intro q r
      rw [Nat.cast_add, Nat.cast_one, recurrence, ih, ih, add_zero]
  have negative (distance : ℕ) : ∀ magnitude : ℕ, ∀ q : ℤ,
      E (-(magnitude : ℤ)) q ((cutoff : ℤ)-distance) = 0 := by
    induction distance with
    | zero => intro magnitude q; exact highSeed _ _ _ (by omega)
    | succ distance outer =>
      intro magnitude
      induction magnitude with
      | zero => intro q; exact zeroSeed _ _
      | succ magnitude inner =>
        intro q
        have law := recurrence (-((magnitude+1:ℕ):ℤ)) (q-1)
          ((cutoff : ℤ)-(distance+1:ℕ))
        rw [show -((magnitude+1:ℕ):ℤ)+1 = -(magnitude:ℤ) by omega,
          show q-1+1 = q by omega,
          show (cutoff : ℤ)-(distance+1:ℕ)+1 = (cutoff : ℤ)-distance by omega,
          inner, outer, add_zero] at law
        exact law.symm
  have allIndices : E p q r = 0 := by
    by_cases hp : 0 ≤ p
    · obtain ⟨degree, rfl⟩ := Int.eq_ofNat_of_zero_le hp
      exact positive degree q r
    · by_cases hr : (cutoff : ℤ) ≤ r
      · exact highSeed p q r hr
      · have pe : p = -((-p).toNat : ℤ) := by omega
        have re : r = (cutoff : ℤ)-(((cutoff : ℤ)-r).toNat : ℤ) := by omega
        rw [pe, re]
        exact negative _ _ q
  obtain ⟨hl, hf, hs⟩ := sequence_supports A B U p q r x KU tail
  refine ⟨hl.smul_right _, hf.smul_right _, (hs.smul_right _).smul_right _, ?_⟩
  apply sub_eq_zero.mp
  change (_-_) + _ = 0 at allIndices
  calc
    _ = discrepancy A B U s p q r x := by unfold discrepancy; abel
    _ = 0 := allIndices

private theorem inverse_of_full (A B : VertexOperator ℂ M)
    (U : ℤ → VertexOperator ℂ M) (s : ℤ) (KU KR : ℕ)
    (tail : ∀ t : ℤ, (KU : ℤ) ≤ t → U t = 0)
    (valid : Valid A B KR) (law : fullLaw A B U s) (r : ℤ) :
    U r = Q A B s r KR := by
  classical
  apply ext_modes
  intro n
  apply LinearMap.ext
  intro x
  let N := (((max KU KR : ℕ) : ℤ)-r).toNat+1
  have boundU : (KU : ℤ) ≤ r+N := by dsimp [N]; omega
  have boundR : (KR : ℤ) ≤ r+N := by dsimp [N]; omega
  let v (j : ℕ) := ((U (r+j))[[n-j]]) x
  have vt (j : ℕ) (hj : N ≤ j) : v j = 0 := by
    simp [v, tail (r+j) (by omega)]
  have row (j : ℕ) : (((R A B (r+j))[[n-j]])) x =
      ∑ k ∈ Finset.range N, Ring.choose ((s : ℂ)/2) k • v (j+k) := by
    have h := (law 0 (n-j) (r+j) x).2.2.2
    have ordered := ordered_residue A B 0 (n-j) (r+j) x
    have z0 : Z 0 A = A := by
      apply HVertexOperator.coeff_inj
      funext e
      simp [Z]
    simp only [neg_zero, z0] at ordered
    rw [← ordered] at h
    rw [← h]
    simp only [leftTerm, Int.cast_zero, zero_add]
    have finiteEq : (∑ᶠ k : ℕ, Ring.choose ((s : ℂ)/2) k •
        ((U (r+j+k))[[n-j-k]]) x) =
        ∑ k ∈ Finset.range N, Ring.choose ((s : ℂ)/2) k •
          ((U (r+j+k))[[n-j-k]]) x := by
      apply finsum_eq_sum_of_support_subset
      intro k hk
      by_contra outside
      exact hk (by simp [tail (r+j+k) (by have := Finset.mem_range.not.mp outside; omega)])
    rw [finiteEq]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only [v]
    simp only [v, Nat.cast_add, add_assoc, sub_sub]
  rw [Q_pad A B s r KR N valid boundR]
  simp only [map_sum, Finset.sum_apply, LinearMap.sum_apply, map_smul,
    Pi.smul_apply, LinearMap.smul_apply, Z_mode]
  simp_rw [row]
  rw [finiteConvolution (-(s : ℂ)/2) ((s : ℂ)/2) N v vt,
    show -(s : ℂ)/2 + (s : ℂ)/2 = 0 by ring]
  rw [Finset.sum_eq_single 0]
  · simp [v]
  · intro j hj hne
    rcases j with _ | j
    · exact (hne rfl).elim
    · simp
  · simp [N]

end D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus
