/- GID: D5/S3/Quantum/Fermionic/BcGhostOppositeNormalProduct
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/BcGhostOppositeNormalProduct
   mirror-E: none(waiver:algebraic-original-ghost-opposite-modes)
   anchors: []
   utility: none
   digest: The opposite normal-product law on the original ghost Fock space. -/

import D5.S3.Quantum.Fermionic.BcGhostDividedL1
import D5.S3.Quantum.Fermionic.BcGhostRelativeEnergy
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTGhostDerivativeBPZ

/-! Opposite fields and signed normal ordering on the original ghost occupations. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators VertexOperator

noncomputable section
namespace D5.S3.Quantum.Fermionic.BcGhostOppositeNormalProduct

open CountableOccupationFock (Fock ket parity)
open BcGhostStateField (Y stateField_parity)
open BcGhostVirasoro (L)
open BcGhostConformalBRSTState (Omega conformal_modes)
open D5.S3.VertexAlgebra.StateFieldResidueReconstruction (integerBinomial epsilon)
open D5.S3.VertexAlgebra.StateField.BorcherdsPermutations (dividedTranslation)
open Finset (range)
open Finset.HasAntidiagonal (antidiagonal mem_antidiagonal)
open private parity_ket from D5.S3.Quantum.Fermionic.CountableOccupationFock

local notation "D" => dividedTranslation (L 1)

private abbrev modeMap (n : ℤ) : Fock →ₗ[ℂ] Module.End ℂ Fock :=
  (LinearMap.proj n).comp (VertexOperator.ncoeff.comp Y)

private abbrev mode (u : Fock) (n : ℤ) (x : Fock) : Fock := modeMap n u x

@[local simp] private theorem mode_zero_left (n : ℤ) (x : Fock) : mode 0 n x = 0 := by
  simp only [mode, map_zero, LinearMap.zero_apply]

@[local simp] private theorem mode_zero_right (u : Fock) (n : ℤ) : mode u n 0 = 0 :=
  (modeMap n u).map_zero

/-- The coefficient of the original ghost opposite field at integral weight, given by
the divided Möbius transform. For homogeneous states its support is finite. -/
def oppositeMode (u : Fock) (h n : ℤ) (x : Fock) : Fock :=
  epsilon h • ∑ᶠ a : ℕ, ((Y (D a u))[[2 * h - n - a - 2]]) x

private theorem finsum_range {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (N : ℕ) (h : ∀ i, N ≤ i → f i = 0) :
    ∑ᶠ i, f i = ∑ i ∈ range N, f i := by
  apply finsum_eq_sum_of_support_subset
  intro i hi
  exact Finset.mem_range.mpr (lt_of_not_ge fun hn => hi (h i hn))

private theorem oppositeMode_eq_sum (u x : Fock) (h n : ℤ) (A : ℕ)
    (hA : ∀ a, A ≤ a → D a u = 0) :
    oppositeMode u h n x = epsilon h • ∑ a ∈ range A, mode (D a u) (2 * h - n - a - 2) x := by
  unfold oppositeMode
  change epsilon h • (∑ᶠ a : ℕ, mode (D a u) (2 * h - n - a - 2) x) = _
  rw [finsum_range _ A (fun a ha => by simp only [hA a ha, mode_zero_left])]

open private raises_lower_weight from D5.S3.Quantum.Fermionic.BcGhostDividedL1

private theorem below_ground_eq_zero (u : Fock) (h : ℤ) (hh : h < -1)
    (hu : L 0 u = (h : ℂ) • u) : u = 0 := by
  ext S
  have hE := BcGhostRelativeEnergy.relativeEnergy_nonneg S
  have hne : BcGhostRelativeEnergy.energy S ≠ h := by
    unfold BcGhostRelativeEnergy.relativeEnergy at hE
    omega
  have hcoeff := BcGhostRelativeEnergy.L_zero_coefficient u S
  rw [hu, Finsupp.smul_apply, smul_eq_mul] at hcoeff
  have hc : ((h : ℂ) - (BcGhostRelativeEnergy.energy S : ℂ)) * u S = 0 := by
    rw [sub_mul, hcoeff, sub_self]
  have hz : (h : ℂ) - (BcGhostRelativeEnergy.energy S : ℂ) ≠ 0 :=
    sub_ne_zero.mpr (Int.cast_injective.ne hne.symm)
  simpa using (mul_eq_zero.mp hc).resolve_left hz

/-- Integral energy and the occupation ground bound give a uniform positive
cutoff for the divided L(1) descendants of a homogeneous ghost state. -/
theorem dividedL1_eq_zero (u : Fock) (h : ℤ) (hu : L 0 u = (h : ℂ) • u)
    (a : ℕ) (ha : max 1 (h + 2).toNat ≤ a) : D a u = 0 := by
  have hp (j : ℕ) : L 0 ((L 1 ^ j) u) = ((h - j : ℤ) : ℂ) • (L 1 ^ j) u := by
    induction j with
    | zero => simpa using hu
    | succ j ih =>
        rw [pow_succ', Module.End.mul_apply, show h - (j + 1 : ℕ) = h - j - 1 by omega]
        exact raises_lower_weight _ _ ih
  have hlow : h - (a : ℤ) < -1 := by omega
  simp [dividedTranslation, below_ground_eq_zero _ _ hlow (hp a)]

private theorem L1_parity (u : Fock) : parity (L 1 u) = L 1 (parity u) := by
  have hΩ : parity Omega = Omega := by
    norm_num [Omega, map_add, map_smul, parity_ket]
  have hL : (Y Omega)[[2]] = L 1 := by simpa using conformal_modes 1
  have hp := stateField_parity Omega 2
  rw [hΩ, hL] at hp
  exact LinearMap.congr_fun hp u

private theorem divided_parity (u : Fock) (p a : ℕ) (hu : parity u = (-1 : ℂ) ^ p • u) :
    parity (D a u) = (-1 : ℂ) ^ p • D a u := by
  have hp (j : ℕ) : parity ((L 1 ^ j) u) = (-1 : ℂ) ^ p • (L 1 ^ j) u := by
    induction j with
    | zero => simpa using hu
    | succ j ih => rw [pow_succ', Module.End.mul_apply, L1_parity, ih, map_smul]
  simp only [dividedTranslation, LinearMap.smul_apply, map_smul, hp,
    smul_comm ((a.factorial : ℂ)⁻¹)]

private theorem sum_triples {M : Type*} [AddCommMonoid M] (f : ℕ → ℕ → ℕ → M) (A B T : ℕ)
    (hf : ∀ a b t, A ≤ a ∨ B ≤ b ∨ T ≤ t → f a b t = 0) :
    (∑ j ∈ range (A + B + T), ∑ c ∈ antidiagonal j,
      ∑ d ∈ antidiagonal c.1, f d.1 d.2 c.2) =
      ∑ a ∈ range A, ∑ b ∈ range B, ∑ t ∈ range T, f a b t := by
  simp_rw [Finset.sum_sigma']
  refine Finset.sum_bij_ne_zero (fun z _ _ => ⟨z.2.2.1, ⟨z.2.2.2, z.2.1.2⟩⟩) ?_ ?_ ?_ ?_
  · intro z _ hz
    simpa only [Finset.mem_sigma, Finset.mem_range, not_le] using
      (not_or.mp (mt (hf _ _ _) hz)).imp_right not_or.mp
  · rintro ⟨j, ⟨⟨c, t⟩, a, b⟩⟩ hz _ ⟨j', ⟨⟨c', t'⟩, a', b'⟩⟩ hz' _ he
    simp only [Finset.mem_sigma, mem_antidiagonal] at hz hz'
    obtain ⟨rfl, rfl, rfl⟩ := by simpa using he
    obtain rfl : c = c' := by omega
    obtain rfl : j = j' := by omega
    rfl
  · rintro ⟨a, b, t⟩ hz hn
    simp only [Finset.mem_sigma, Finset.mem_range] at hz
    refine ⟨⟨a + b + t, ⟨(a + b, t), (a, b)⟩⟩, ?_, hn, rfl⟩
    simp only [Finset.mem_sigma, Finset.mem_range, mem_antidiagonal, and_true]
    omega
  · intros
    rfl

open private reflect_choose from D5.S3.VertexAlgebra.StateField.BorcherdsPermutations

private theorem minus_one_binomial (i : ℕ) : (-1 : ℂ) ^ i * integerBinomial (-1) i = 1 := by
  have hcast (z : ℤ) : integerBinomial z i = Ring.choose (z : ℂ) i :=
    Ring.map_choose (Int.castRingHom ℂ) z i
  rw [hcast, Int.cast_neg, Int.cast_one, reflect_choose,
    show -(-1 : ℂ) + i - 1 = (i : ℂ) by ring,
    Ring.choose_natCast, Nat.choose_self, Nat.cast_one]

private def firstTerm (u v x : Fock) (P Q : ℤ) (i : ℕ) : Fock :=
  mode u (P - 1 - i) (mode v (Q + i) x)

private def secondTerm (u v x : Fock) (P Q : ℤ) (i : ℕ) : Fock :=
  mode v (Q - 1 - i) (mode u (P + i) x)

private theorem borcherds_minus_one (u v x : Fock) (p q : ℕ)
    (hu : parity u = (-1 : ℂ) ^ p • u) (hv : parity v = (-1 : ℂ) ^ q • v)
    (P Q : ℤ) (T I : ℕ)
    (hT : ∀ t : ℕ, T ≤ t → mode u ((t : ℤ) - 1) v = 0)
    (hI : ∀ i : ℕ, I ≤ i → mode v (Q + i) x = 0 ∧ mode u (P + i) x = 0) :
    ∑ t ∈ range T, integerBinomial P t • mode (mode u ((t : ℤ) - 1) v) (P + Q - t) x =
      ∑ i ∈ range I, (firstTerm u v x P Q i +
        (-1 : ℂ) ^ (p * q) • secondTerm u v x P Q i) := by
  have H := (BcGhostBorcherds.borcherds u v x p q hu hv P Q (-1)).2.2.2
  have he : epsilon (-1) = -1 := by norm_num [epsilon]
  simp only [BcGhostBorcherds.jacobiLeftTerm, minus_one_binomial, one_smul, he, neg_one_mul,
    neg_smul, sub_neg_eq_add, show ∀ t : ℕ, (-1 : ℤ) + t = (t : ℤ) - 1 by intro; omega] at H
  change (∑ᶠ t : ℕ, integerBinomial P t •
      mode (mode u ((t : ℤ) - 1) v) (P + Q - t) x) =
    ∑ᶠ i : ℕ, (firstTerm u v x P Q i + (-1 : ℂ) ^ (p * q) • secondTerm u v x P Q i) at H
  rw [finsum_range _ T, finsum_range _ I] at H
  · exact H
  · intro i hi
    simp [firstTerm, secondTerm, (hI i hi).1, (hI i hi).2]
  · intro t ht
    rw [hT t ht]
    simp

private theorem uniform_range (A B : ℕ) (f : ℕ → ℕ → ℤ)
    (r : ℤ) : ∃ N : ℕ, ∀ a ∈ range A, ∀ b ∈ range B, ∀ j : ℕ, N ≤ j →
    f a b < r + j := by
  classical
  let box := range A ×ˢ range B
  let bound (ab : ℕ × ℕ) := (f ab.1 ab.2 - r).toNat + 1
  refine ⟨box.sup bound, ?_⟩
  intro a ha b hb j hj
  have hab : (a, b) ∈ box := Finset.mem_product.mpr ⟨ha, hb⟩
  have hle := (Finset.le_sup (f := bound) hab).trans hj
  dsimp [bound] at hle
  omega

private theorem mode_vanish_of_order (u x : Fock) (n : ℤ)
    (hn : -((HahnModule.of ℂ).symm ((Y u) x)).order < n) : mode u n x = 0 := by
  change ((Y u)[[n]]) x = 0
  apply VertexOperator.ncoeff_eq_zero_of_lt_order
  omega

private theorem opposite_composition (u v x : Fock) (h k n : ℤ) (s : ℂ)
    (A B : ℕ) (hA : ∀ a, A ≤ a → D a u = 0) (hB : ∀ b, B ≤ b → D b v = 0)
    (i : ℕ) :
    oppositeMode u h i (oppositeMode v k (n - 1 - i) x) +
        s • oppositeMode v k (n + i) (oppositeMode u h (-1 - i) x) =
      epsilon (h + k) • ∑ a ∈ range A, ∑ b ∈ range B,
        (firstTerm (D a u) (D b v) x (2 * h - a - 1) (2 * k - b - n - 1) i +
          s • secondTerm (D a u) (D b v) x (2 * h - a - 1) (2 * k - b - n - 1) i) := by
  simp_rw [oppositeMode_eq_sum u _ _ _ A hA, oppositeMode_eq_sum v _ _ _ B hB,
    map_smul, map_sum, ← Finset.smul_sum]
  have hsign : epsilon h * epsilon k = epsilon (h + k) :=
    (zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0) h k).symm
  have hsign' : epsilon k * epsilon h = epsilon (h + k) := (mul_comm _ _).trans hsign
  simp only [smul_smul (epsilon h) (epsilon k), smul_smul (epsilon k) (epsilon h), hsign, hsign']
  rw [smul_comm s (epsilon (h + k)), ← smul_add]
  congr 1
  simp only [Finset.sum_add_distrib, Finset.smul_sum]
  rw [Finset.sum_comm (s := range B) (t := range A)]
  congr 1
  · apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    unfold firstTerm
    rw [show 2 * h - i - a - 2 = 2 * h - a - 1 - 1 - i by omega,
      show 2 * k - (n - 1 - i) - b - 2 = 2 * k - b - n - 1 + i by omega]
  · apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    unfold secondTerm
    rw [show 2 * k - (n + i) - b - 2 = 2 * k - b - n - 1 - 1 - i by omega,
      show 2 * h - (-1 - i) - a - 2 = 2 * h - a - 1 + i by omega]

set_option maxHeartbeats 1500000 in
-- Bound and reindex the three descendant sums before the Borcherds substitution.
/-- The original ghost opposite coefficient of a `(-1)`-product is its
signed reverse normal product. Both cutoffs and finite support are derived from
the occupation ghost fields and their integral energy bounds. -/
theorem oppositeMode_normal_product (u v x : Fock) (h k n : ℤ) (p q : ℕ)
    (hu : L 0 u = (h : ℂ) • u) (hv : L 0 v = (k : ℂ) • v)
    (hpu : parity u = (-1 : ℂ) ^ p • u) (hpv : parity v = (-1 : ℂ) ^ q • v) :
    let term := fun i : ℕ =>
      oppositeMode u h i (oppositeMode v k (n - 1 - i) x) +
        (-1 : ℂ) ^ (p * q) • oppositeMode v k (n + i) (oppositeMode u h (-1 - i) x)
    Function.HasFiniteSupport term ∧
      oppositeMode (((Y u)[[-1]]) v) (h + k) n x = ∑ᶠ i : ℕ, term i := by
  classical
  let A := max 1 (h + 2).toNat
  let B := max 1 (k + 2).toNat
  have hA : ∀ a, A ≤ a → D a u = 0 := dividedL1_eq_zero u h hu
  have hB : ∀ b, B ≤ b → D b v = 0 := dividedL1_eq_zero v k hv
  let order (w y : Fock) := -((HahnModule.of ℂ).symm ((Y w) y)).order
  let P (a : ℕ) : ℤ := 2 * h - a - 1
  let Q (b : ℕ) : ℤ := 2 * k - b - n - 1
  let sign : ℂ := (-1 : ℂ) ^ (p * q)
  obtain ⟨T, hT⟩ := uniform_range A B (fun a b => order (D a u) (D b v)) (-1)
  obtain ⟨I, hI⟩ := uniform_range A B
    (fun a b => max (order (D b v) x - Q b) (order (D a u) x - P a)) 0
  have contraction (a b t : ℕ) (ht : A ≤ a ∨ B ≤ b ∨ T ≤ t) :
      mode (D a u) ((t : ℤ) - 1) (D b v) = 0 := by
    by_cases ha : a ∈ range A
    · by_cases hb : b ∈ range B
      · have ht' : T ≤ t := by simp only [Finset.mem_range] at ha hb; omega
        apply mode_vanish_of_order
        have hh := hT a ha b hb t ht'
        dsimp [order] at hh
        omega
      · simp only [hB b (by simpa using hb), mode_zero_right]
    · simp only [hA a (by simpa using ha), mode_zero_left]
  have rightmost (a : ℕ) (ha : a ∈ range A) (b : ℕ) (hb : b ∈ range B)
      (i : ℕ) (hi : I ≤ i) :
      mode (D b v) (Q b + i) x = 0 ∧ mode (D a u) (P a + i) x = 0 := by
    have hh := hI a ha b hb i hi
    dsimp [order] at hh
    constructor <;> apply mode_vanish_of_order <;> omega
  have productBound (j : ℕ) (hj : A + B + T ≤ j) : D j (mode u (-1) v) = 0 := by
    rw [show mode u (-1) v = ((Y u)[[-1]]) v from rfl,
      BcGhostDividedL1.dividedL1_mode_product u v h (-1) j hu]
    apply Finset.sum_eq_zero
    intro c hc
    apply Finset.sum_eq_zero
    intro d hd
    have hc' := mem_antidiagonal.mp hc
    have hd' := mem_antidiagonal.mp hd
    change integerBinomial _ _ • mode (D d.1 u) ((-1 : ℤ) + c.2) (D d.2 v) = 0
    rw [show (-1 : ℤ) + c.2 = (c.2 : ℤ) - 1 by omega, contraction _ _ _ (by omega), smul_zero]
  let term (i : ℕ) :=
    oppositeMode u h i (oppositeMode v k (n - 1 - i) x) +
      sign • oppositeMode v k (n + i) (oppositeMode u h (-1 - i) x)
  have hterm (i : ℕ) (hi : I ≤ i) : term i = 0 := by
    dsimp only [term]
    rw [opposite_composition u v x h k n sign A B hA hB]
    suffices (∑ a ∈ range A, ∑ b ∈ range B, (firstTerm (D a u) (D b v) x (P a) (Q b) i +
        sign • secondTerm (D a u) (D b v) x (P a) (Q b) i)) = 0 by rw [this, smul_zero]
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    simp [firstTerm, secondTerm, (rightmost a ha b hb i hi).1, (rightmost a ha b hb i hi).2]
  change Function.HasFiniteSupport term ∧ oppositeMode (mode u (-1) v) (h + k) n x = _
  refine ⟨(range I).finite_toSet.subset (fun i hi => ?_), ?_⟩
  · exact Finset.mem_range.mpr (lt_of_not_ge fun hn => hi (hterm i hn))
  rw [finsum_range term I hterm, oppositeMode_eq_sum _ _ _ _ _ productBound]
  dsimp only [term]
  simp_rw [opposite_composition u v x h k n sign A B hA hB]
  rw [← Finset.smul_sum]
  congr 1
  let f (a b t : ℕ) := integerBinomial (P a) t •
    mode (mode (D a u) ((t : ℤ) - 1) (D b v)) (P a + Q b - t) x
  calc
    (∑ j ∈ range (A + B + T), mode (D j (mode u (-1) v)) (2 * (h + k) - n - j - 2) x) =
        ∑ j ∈ range (A + B + T), ∑ c ∈ antidiagonal j,
          ∑ d ∈ antidiagonal c.1, f d.1 d.2 c.2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [show mode u (-1) v = ((Y u)[[-1]]) v from rfl,
        BcGhostDividedL1.dividedL1_mode_product u v h (-1) j hu]
      simp only [mode, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro d hd
      have hc' := mem_antidiagonal.mp hc
      have hd' := mem_antidiagonal.mp hd
      unfold f P Q
      rw [show 2 * h - (-1) - d.1 - 2 = 2 * h - d.1 - 1 by omega,
        show (-1 : ℤ) + c.2 = (c.2 : ℤ) - 1 by omega,
        show 2 * (h + k) - n - j - 2 = (2 * h - d.1 - 1) + (2 * k - d.2 - n - 1) - c.2 by omega]
      rfl
    _ = ∑ a ∈ range A, ∑ b ∈ range B, ∑ t ∈ range T, f a b t :=
      sum_triples f A B T (fun a b t ht => by simp [f, contraction a b t ht])
    _ = _ := by
      rw [Finset.sum_comm (s := range I) (t := range A)]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm (s := range I) (t := range B)]
      apply Finset.sum_congr rfl
      intro b hb
      exact borcherds_minus_one (D a u) (D b v) x p q (divided_parity u p a hpu)
        (divided_parity v q b hpv) (P a) (Q b) T I
        (fun t ht => contraction a b t (Or.inr (Or.inr ht)))
        (rightmost a ha b hb)

#print axioms dividedL1_eq_zero
#print axioms oppositeMode_normal_product

open D5.S3.VertexAlgebra.OriginalOrbifoldBRSTGhostBPZ (beta)

private theorem parity_pow_mode (u x : Fock) (n : ℤ) (p r : ℕ)
    (hu : parity u = (-1 : ℂ) ^ p • u) :
    (parity ^ r) (mode u n x) = (-1 : ℂ) ^ (r * p) • mode u n ((parity ^ r) x) := by
  have pass (y : Fock) : parity (mode u n y) = (-1 : ℂ) ^ p • mode u n (parity y) := by
    have hp := LinearMap.congr_fun (stateField_parity u n) y
    change parity (mode u n y) = mode (parity u) n (parity y) at hp
    rw [hp, hu]
    simp only [mode, map_smul, LinearMap.smul_apply]
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ' parity, Module.End.mul_apply, ih, map_smul, pass, smul_smul, ← pow_add,
      Nat.succ_mul, Module.End.mul_apply]

/-- BPZ adjunction for all modes of a fixed integral weight and parity. -/
def HasBPZAdjunction (u : Fock) (h : ℤ) (p : ℕ) : Prop :=
  ∀ (n : ℤ) (x y : Fock), beta (((Y u)[[n]]) x) y =
    beta ((parity ^ p) x) (oppositeMode u h n y)

private theorem beta_mode_composition (u v x y : Fock) (h k a b : ℤ) (p q : ℕ)
    (hpv : parity v = (-1 : ℂ) ^ q • v)
    (bu : HasBPZAdjunction u h p) (bv : HasBPZAdjunction v k q) :
    beta (mode u a (mode v b x)) y =
      (-1 : ℂ) ^ (p * q) * beta ((parity ^ (p + q)) x)
        (oppositeMode v k b (oppositeMode u h a y)) := by
  have bu' : ∀ z w, beta (mode u a z) w = beta ((parity ^ p) z) (oppositeMode u h a w) := bu a
  have bv' : ∀ z w, beta (mode v b z) w = beta ((parity ^ q) z) (oppositeMode v k b w) := bv b
  rw [bu', parity_pow_mode v x b q p hpv, map_smul, LinearMap.smul_apply, smul_eq_mul, bv',
    ← Module.End.mul_apply, ← pow_add, add_comm q p]

private theorem normal_product (u v x : Fock) (n : ℤ) (p q : ℕ)
    (hpu : parity u = (-1 : ℂ) ^ p • u) (hpv : parity v = (-1 : ℂ) ^ q • v) :
    let term := fun i => firstTerm u v x 0 n i + (-1 : ℂ) ^ (p * q) • secondTerm u v x 0 n i
    Function.HasFiniteSupport term ∧ mode (mode u (-1) v) n x = ∑ᶠ i : ℕ, term i := by
  have H := BcGhostStateFieldIterate.stateField_iterate u v x p q hpu hpv (-1) n
  dsimp only at H
  have hchoose (i : ℕ) : (-1 : ℂ) ^ i * ((Ring.choose (-1 : ℤ) i : ℤ) : ℂ) = 1 :=
    minus_one_binomial i
  simp only [hchoose, one_smul, show (-1 : ℂ) ^ (-1 : ℤ) = -1 by norm_num,
    neg_one_mul, neg_smul, sub_neg_eq_add] at H
  let first := firstTerm u v x 0 n
  let second := secondTerm u v x 0 n
  let sign : ℂ := (-1 : ℂ) ^ (p * q)
  simp only [show (-1 : ℤ) + n = n - 1 by omega] at H
  change Function.HasFiniteSupport (fun i : ℕ => mode u (-1 - i) (mode v (n + i) x)) ∧
    Function.HasFiniteSupport (fun i : ℕ => mode v (n - 1 - i) (mode u i x)) ∧
    mode (mode u (-1) v) n x =
      (∑ᶠ i : ℕ, mode u (-1 - i) (mode v (n + i) x)) +
        sign • (∑ᶠ i : ℕ, mode v (n - 1 - i) (mode u i x)) at H
  have hfirst : first = fun i : ℕ => mode u (-1 - i) (mode v (n + i) x) := by
    funext i
    simp only [first, firstTerm, zero_sub]
  have hsecond : second = fun i : ℕ => mode v (n - 1 - i) (mode u i x) := by
    funext i
    simp only [second, secondTerm, zero_add]
  have hf : Function.HasFiniteSupport first := hfirst.symm ▸ H.1
  have hs : Function.HasFiniteSupport second := hsecond.symm ▸ H.2.1
  have hs' : Function.HasFiniteSupport (fun i => sign • second i) :=
    hs.fun_comp (smul_zero sign)
  have H' : mode (mode u (-1) v) n x = (∑ᶠ i, first i) + sign • (∑ᶠ i, second i) := by
    rw [hfirst, hsecond]
    exact H.2.2
  dsimp only
  exact ⟨hf.add hs', H'.trans (by rw [finsum_add_distrib hf hs', smul_finsum' sign hs])⟩

/-- Adjunction for the actual absolute ghost BPZ form is closed under the
native normal product. The parity operators act on the first input. -/
theorem beta_normal_product (u v : Fock) (h k : ℤ) (p q : ℕ)
    (hu : L 0 u = (h : ℂ) • u) (hv : L 0 v = (k : ℂ) • v)
    (hpu : parity u = (-1 : ℂ) ^ p • u) (hpv : parity v = (-1 : ℂ) ^ q • v)
    (bu : HasBPZAdjunction u h p) (bv : HasBPZAdjunction v k q) :
    HasBPZAdjunction (((Y u)[[-1]]) v) (h + k) (p + q) := by
  intro n x y
  obtain ⟨hf, hn⟩ := normal_product u v x n p q hpu hpv
  obtain ⟨hg, ho⟩ := oppositeMode_normal_product u v y h k n p q hu hv hpu hpv
  let f : Fock →ₗ[ℂ] ℂ := (LinearMap.applyₗ (R := ℂ) y).comp beta
  let g : Fock →ₗ[ℂ] ℂ := beta ((parity ^ (p + q)) x)
  change f (mode (mode u (-1) v) n x) = g (oppositeMode (mode u (-1) v) (h + k) n y)
  rw [hn, show oppositeMode (mode u (-1) v) (h + k) n y = _ from ho,
    map_finsum f hf, map_finsum g hg]
  congr 1
  funext i
  rw [f.map_add, f.map_smul, g.map_add, g.map_smul]
  simp only [firstTerm, secondTerm, zero_sub, zero_add, smul_eq_mul]
  let sign : ℂ := (-1 : ℂ) ^ (p * q)
  change beta (mode u (-1 - i) (mode v (n + i) x)) y +
      sign * beta (mode v (n - 1 - i) (mode u i x)) y =
    beta ((parity ^ (p + q)) x) (oppositeMode u h i (oppositeMode v k (n - 1 - i) y)) +
      sign * beta ((parity ^ (p + q)) x) (oppositeMode v k (n + i) (oppositeMode u h (-1 - i) y))
  have sq : (-1 : ℂ) ^ (p * q) * (-1 : ℂ) ^ (p * q) = 1 := by
    rw [← mul_pow]
    norm_num
  dsimp only [sign]
  rw [beta_mode_composition u v x y h k _ _ p q hpv bu bv,
    beta_mode_composition v u x y k h _ _ q p hpu bv bu,
    mul_comm q p, add_comm q p, ← mul_assoc, sq, one_mul]
  exact add_comm _ _

#print axioms beta_normal_product

open CountableOccupationFock (vacuum create create_ket phase lowerCount)
open BcGhostRelativeEnergy (energy siteEnergy L_zero_ket siteEnergy_even siteEnergy_odd)
open D5.S3.VertexAlgebra.OriginalOrbifoldBRSTGhostDerivativeBPZ
  (site siteWeight site_L0 site_parity site_L1_pow_eq_zero beta_site_mode)
open private site_modes from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTGhostDerivativeBPZ
open private generatingMode from D5.S3.Quantum.Fermionic.BcGhostStateField
open private L_vacuum_nonneg from D5.S3.Quantum.Fermionic.BcGhostVirasoro
open private identity_modes from D5.S3.Quantum.Fermionic.BcGhostConformalBRSTState

private theorem beta_vacuum : HasBPZAdjunction vacuum 0 0 := by
  have hcut (a : ℕ) (ha : 1 ≤ a) : D a vacuum = 0 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
    simp only [dividedTranslation, LinearMap.smul_apply, pow_succ, Module.End.mul_apply,
      L_vacuum_nonneg 1 (by norm_num), map_zero, smul_zero]
  intro n x y
  rw [oppositeMode_eq_sum _ _ _ _ 1 hcut, Finset.sum_range_one]
  simp only [pow_zero, Module.End.one_apply, epsilon, one_smul, dividedTranslation,
    Nat.factorial_zero, Nat.cast_one, inv_one, Int.natCast_zero,
    mul_zero, sub_zero, zero_sub, zpow_zero]
  change beta (((Y vacuum)[[n]]) x) y = beta x (((Y vacuum)[[-n - 2]]) y)
  rw [BcGhostStateField.stateField_creation.1, identity_modes, identity_modes]
  by_cases hn : n = -1
  · simp [hn]
  · simp [hn, show -n - 2 ≠ -1 by omega]

private theorem beta_site (species : Bool) (t : ℕ) :
    HasBPZAdjunction (site species t) (siteWeight species t) 1 := by
  intro n x y
  have hcut (a : ℕ) (ha : t + 1 ≤ a) : D a (site species t) = 0 := by
    simp only [dividedTranslation, LinearMap.smul_apply,
      site_L1_pow_eq_zero species t a (by omega), smul_zero]
  rw [oppositeMode_eq_sum _ _ _ _ (t + 1) hcut]
  simp only [mode, dividedTranslation, LinearMap.smul_apply, map_smul,
    epsilon, pow_one, smul_eq_mul]
  have H := beta_site_mode species t n x y
  simp only [LinearMap.sum_apply, map_smul, Pi.smul_apply, LinearMap.smul_apply] at H
  exact H

private theorem site_index_weight (species : Bool) (t : ℕ) :
    siteWeight species t = siteEnergy (2 * t + if species then 1 else 0) := by
  cases species <;> simp [siteWeight, siteEnergy_even, siteEnergy_odd] <;> omega

private theorem site_creation (species : Bool) (t : ℕ) (v : Fock) :
    mode (site species t) (-1) v = create (2 * t + if species then 1 else 0) v := by
  change ((Y (site species t))[[-1]]) v = _
  rw [site_modes]
  simp only [show -(-1 : ℤ) - 1 + t = (t : ℤ) by omega,
    Int.cast_natCast, Ring.choose_natCast, Nat.choose_self, Nat.cast_one, one_smul]
  cases species
  · change BcGhostFock.b (-1 - t - 1) v = create (2 * t + 0) v
    rw [show (-1 : ℤ) - t - 1 = -(t : ℤ) - 2 by omega, (BcGhostFock.mode_correspondence t).1,
      Nat.add_zero]
  · change BcGhostFock.c (-1 - t + 2) v = create (2 * t + 1) v
    rw [show (-1 : ℤ) - t + 2 = 1 - (t : ℤ) by omega,
      (BcGhostFock.mode_correspondence t).2.2.1]

/-- The signed BPZ mode adjunction on each native occupation ket. -/
theorem beta_occupation_mode (S : Finset ℕ) :
    HasBPZAdjunction (ket S) (energy S) S.card := by
  classical
  induction S using Finset.eraseInduction with
  | H S ih =>
    by_cases hempty : S = ∅
    · subst S
      simpa [energy, vacuum] using beta_vacuum
    · have hS := Finset.nonempty_iff_ne_empty.mpr hempty
      let j := S.min' hS
      let tail := S.erase j
      let t := j / 2
      let species := j % 2 == 1
      have hj : j ∈ S := Finset.min'_mem S hS
      have hnot : j ∉ tail := Finset.notMem_erase j S
      have hinsert : insert j tail = S := Finset.insert_erase hj
      have hindex : 2 * t + (if species then 1 else 0) = j := by
        rcases Nat.mod_two_eq_zero_or_one j with h | h <;> simp [t, species, h] <;> omega
      have hphase : phase j tail = 1 := by
        have hz : tail.filter (· < j) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro l hl
          obtain ⟨hl, hlt⟩ := Finset.mem_filter.mp hl
          exact (not_lt_of_ge (Finset.min'_le S l (Finset.mem_of_mem_erase hl))) hlt
        simp [phase, lowerCount, hz]
      have hstate : mode (site species t) (-1) (ket tail) = ket S := by
        rw [site_creation, hindex, create_ket, ite_eq_right hnot, hphase, one_smul, hinsert]
      have hweight : siteWeight species t + energy tail = energy S := by
        have hw := site_index_weight species t
        rw [hindex] at hw
        have he : energy (insert j tail) = siteEnergy j + energy tail :=
          Finset.sum_insert hnot
        rw [hinsert] at he
        exact (congrArg (· + energy tail) hw).trans he.symm
      have hcard : 1 + tail.card = S.card := by
        have hc := Finset.card_insert_of_notMem hnot
        rw [hinsert] at hc
        omega
      have hb := beta_normal_product (site species t) (ket tail)
        (siteWeight species t) (energy tail) 1 tail.card
        (site_L0 species t) (L_zero_ket tail)
        (by simpa using site_parity species t) (parity_ket tail)
        (beta_site species t) (ih j hj)
      change HasBPZAdjunction (mode (site species t) (-1) (ket tail))
        (siteWeight species t + energy tail) (1 + tail.card) at hb
      exact hstate ▸ hweight ▸ hcard ▸ hb

#print axioms beta_occupation_mode

private theorem parity_coefficient (u : Fock) (S : Finset ℕ) :
    (parity u) S = (-1 : ℂ) ^ S.card * u S := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      simp only [map_add, Finsupp.add_apply, hf, hg, mul_add]
  | single T a =>
      have hsingle : Finsupp.single T a = a • ket T := by simp [ket]
      rw [hsingle, map_smul, parity_ket]
      by_cases hTS : T = S
      · subst S
        simp [ket, mul_comm]
      · simp [ket, Ne.symm hTS]

private theorem parity_pow_eq_of_sign_eq (p q : ℕ)
    (hsign : (-1 : ℂ) ^ p = (-1 : ℂ) ^ q) : parity ^ p = parity ^ q := by
  rw [neg_one_pow_eq_pow_mod_two p, neg_one_pow_eq_pow_mod_two q] at hsign
  have hmod : p % 2 = q % 2 := by
    rcases Nat.mod_two_eq_zero_or_one p with hp | hp <;>
      rcases Nat.mod_two_eq_zero_or_one q with hq | hq
    · exact hp.trans hq.symm
    · norm_num [hp, hq] at hsign
    · norm_num [hp, hq] at hsign
    · exact hp.trans hq.symm
  have htwo : parity ^ (2 : ℕ) = 1 := by
    rw [pow_two, CountableOccupationFock.parity_involution]
  rw [pow_eq_pow_mod p htwo, pow_eq_pow_mod q htwo, hmod]

/-- The signed BPZ mode adjunction on any native ghost state of integral weight
and definite parity. -/
theorem beta_homogeneous_mode (u : Fock) (h : ℤ) (p : ℕ)
    (hu : L 0 u = (h : ℂ) • u) (hpu : parity u = (-1 : ℂ) ^ p • u) :
    HasBPZAdjunction u h p := by
  classical
  intro n x y
  let A := max 1 (h + 2).toNat
  let opposite : Module.End ℂ Fock := epsilon h • ∑ a ∈ range A,
    (LinearMap.applyₗ (R := ℂ) y).comp ((modeMap (2 * h - n - a - 2)).comp (D a))
  have hopposite (v : Fock) (hv : L 0 v = (h : ℂ) • v) :
      oppositeMode v h n y = opposite v := by
    rw [oppositeMode_eq_sum v y h n A (dividedL1_eq_zero v h hv)]
    simp only [opposite, mode, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.applyₗ_apply_apply] <;> rfl
  let left : Fock →ₗ[ℂ] ℂ := ((LinearMap.applyₗ (R := ℂ) y).comp beta).comp
    ((LinearMap.applyₗ (R := ℂ) x).comp (modeMap n))
  let right : Fock →ₗ[ℂ] ℂ := (beta ((parity ^ p) x)).comp opposite
  have hket (S : Finset ℕ) (hS : S ∈ u.support) : left (ket S) = right (ket S) := by
    have hne : u S ≠ 0 := Finsupp.mem_support_iff.mp hS
    have hweight : energy S = h := by
      have hc := BcGhostRelativeEnergy.L_zero_coefficient u S
      rw [hu, Finsupp.smul_apply, smul_eq_mul] at hc
      exact Int.cast_injective (mul_right_cancel₀ hne hc.symm)
    have hsign : (-1 : ℂ) ^ S.card = (-1 : ℂ) ^ p := by
      have hc := parity_coefficient u S
      rw [hpu, Finsupp.smul_apply, smul_eq_mul] at hc
      exact mul_right_cancel₀ hne hc.symm
    have hv : L 0 (ket S) = (h : ℂ) • ket S := by rw [L_zero_ket, hweight]
    have hadj := beta_occupation_mode S n x y
    rw [hweight, parity_pow_eq_of_sign_eq S.card p hsign, hopposite (ket S) hv] at hadj
    exact hadj
  have hexpand : u = ∑ S ∈ u.support, u S • ket S := by
    simpa [Finsupp.sum, ket] using (Finsupp.sum_single u).symm
  rw [hopposite u hu]
  change left u = right u
  rw [hexpand]
  simp only [map_sum, map_smul]
  exact Finset.sum_congr rfl (fun S hS => congrArg (fun z : ℂ => u S • z) (hket S hS))

#print axioms beta_homogeneous_mode

end D5.S3.Quantum.Fermionic.BcGhostOppositeNormalProduct
