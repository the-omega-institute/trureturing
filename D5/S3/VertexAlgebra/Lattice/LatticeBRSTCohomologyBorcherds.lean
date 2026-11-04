/-
SOURCE-ONLY / UNCOMPILED QUOTIENT CONSUMER.

This consumer imports the preserved native LatticeMatterGhostBorcherds supplier,
SHA256 abf47cbebd801af9e60ece238013b4c5824a044a0a9ffd14b1fd7178978194a7,
and its SignedBorcherds supplier, SHA256
c04af6f84042ef6c10160ee9a09d193361af3355967b31b1a226c4554f38aa6c.
The fixed compatible iterate closure and the tensor supplier were genuinely
compiled in the preceding native stage. Their native evidence is distinct
from official acceptance, and does not establish this quotient consumer.

The theorem below DESCENDS that exact proposed all-integer identity. It does
not assume Jacobi as a hypothesis, reproduce its proof, or claim an accepted
Jacobi theorem. The finite-support proofs are preserved before either sum is
mapped, first through the actual kernel subtype and then through its quotient.
Scott Carnahan / original tensor and ghost suppliers retain their attribution.
-/

import D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyNonvacuity
import D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostBorcherds

/-! Finite-support Borcherds descent on the original critical BRST quotient. -/

set_option autoImplicit false

open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.LatticeBRSTCohomologyField

open LatticeGeneratingFieldLocality (LatticeData)
open LatticeMatterGhostCoupling (State)
open StateFieldResidueReconstruction (integerBinomial epsilon)
open FieldNormalProduct (dividedDerivative)
open private minus_two_weight from D5.S3.VertexAlgebra.LatticeActualStateDerivative

noncomputable section

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (h26 : D.rank = 26)
  (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
  (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)

def jacobiLeft (a b c : Cohomology D H h26 hHG hGH) (p q r : ℤ) (i : ℕ) :
    Cohomology D H h26 hHG hGH :=
  integerBinomial p i • mode D H h26 hHG hGH (p + q - i)
    (mode D H h26 hHG hGH (r + i) a b) c

def jacobiForward (a b c : Cohomology D H h26 hHG hGH) (p q r : ℤ) (i : ℕ) :
    Cohomology D H h26 hHG hGH :=
  (((-1 : ℂ)^i) * integerBinomial r i) • mode D H h26 hHG hGH (p + r - i) a
    (mode D H h26 hHG hGH (q + i) b c)

def jacobiReverseEven (a b c : Cohomology D H h26 hHG hGH) (p q r : ℤ) (i : ℕ) :
    Cohomology D H h26 hHG hGH :=
  (((-1 : ℂ)^i) * integerBinomial r i) • mode D H h26 hHG hGH (q + r - i) b
    (mode D H h26 hHG hGH (p + i)
      ((2 : ℂ)⁻¹ • (a + parity D H h26 hHG hGH a)) c)

def jacobiReverseOdd (a b c : Cohomology D H h26 hHG hGH) (p q r : ℤ) (i : ℕ) :
    Cohomology D H h26 hHG hGH :=
  (((-1 : ℂ)^i) * integerBinomial r i) • mode D H h26 hHG hGH (q + r - i)
    (parity D H h26 hHG hGH b)
    (mode D H h26 hHG hGH (p + i)
      ((2 : ℂ)⁻¹ • (a - parity D H h26 hHG hGH a)) c)

private theorem finite_of_cycle_val (f : ℕ → cycles D H)
    (hf : Function.HasFiniteSupport (fun i => (f i : State D))) :
    Function.HasFiniteSupport f := by
  apply hf.subset
  intro i hi hz
  exact hi (Subtype.ext hz)

/-- The genuine unrestricted three-integer identity on the ORIGINAL BRST
quotient, in separated finite sums. Arbitrary parity mixtures are retained.
The original tensor identity is reused without reproving Jacobi. -/
theorem borcherds (a b c : Cohomology D H h26 hHG hGH) (p q r : ℤ) :
    Function.HasFiniteSupport (jacobiLeft D H h26 hHG hGH a b c p q r) ∧
    Function.HasFiniteSupport (jacobiForward D H h26 hHG hGH a b c p q r) ∧
    Function.HasFiniteSupport (jacobiReverseEven D H h26 hHG hGH a b c p q r) ∧
    Function.HasFiniteSupport (jacobiReverseOdd D H h26 hHG hGH a b c p q r) ∧
    (∑ᶠ i : ℕ, jacobiLeft D H h26 hHG hGH a b c p q r i) =
      (∑ᶠ i : ℕ, jacobiForward D H h26 hHG hGH a b c p q r i) -
        epsilon r •
          ((∑ᶠ i : ℕ, jacobiReverseEven D H h26 hHG hGH a b c p q r i) +
            (∑ᶠ i : ℕ, jacobiReverseOdd D H h26 hHG hGH a b c p q r i)) := by
  classical
  obtain ⟨x, rfl⟩ := classOf_surjective D H h26 hHG hGH a
  obtain ⟨y, rfl⟩ := classOf_surjective D H h26 hHG hGH b
  obtain ⟨z, rfl⟩ := classOf_surjective D H h26 hHG hGH c
  let x0 : cycles D H := (2 : ℂ)⁻¹ • (x + cycleParity D H x)
  let x1 : cycles D H := (2 : ℂ)⁻¹ • (x - cycleParity D H x)
  let w : ℕ → ℂ := fun i => ((-1 : ℂ)^i) * integerBinomial r i
  let l : ℕ → cycles D H := fun i =>
    integerBinomial p i • cycleMode D H (p + q - i) (cycleMode D H (r + i) x y) z
  let f : ℕ → cycles D H := fun i =>
    w i • cycleMode D H (p + r - i) x (cycleMode D H (q + i) y z)
  let e : ℕ → cycles D H := fun i =>
    w i • cycleMode D H (q + r - i) y (cycleMode D H (p + i) x0 z)
  let o : ℕ → cycles D H := fun i =>
    w i • cycleMode D H (q + r - i) (cycleParity D H y)
      (cycleMode D H (p + i) x1 z)
  have src := LatticeMatterGhostBorcherds.borcherds D
    (x : State D) (y : State D) (z : State D) p q r
  have hl : Function.HasFiniteSupport l := finite_of_cycle_val D H l src.1
  have hf : Function.HasFiniteSupport f := finite_of_cycle_val D H f src.2.1
  have he : Function.HasFiniteSupport e := finite_of_cycle_val D H e src.2.2.1
  have ho : Function.HasFiniteSupport o := finite_of_cycle_val D H o src.2.2.2.1
  let s : ℕ → cycles D H := fun i => f i - epsilon r • (e i + o i)
  have hs : Function.HasFiniteSupport s :=
    hf.sub ((he.add ho).smul_right (fun _ => epsilon r))
  have original_equality :
      (∑ᶠ i : ℕ, (l i : State D)) = ∑ᶠ i : ℕ, (s i : State D) := by
    calc
      _ = _ := src.2.2.2.2
      _ = _ := by
        apply finsum_congr
        intro i
        dsimp [s, l, f, e, o, w, x0, x1, cycleMode, cycleParity,
          originalMode, LatticeMatterGhostSignedBorcherds.mu_D]
        module
  have cycle_equality : (∑ᶠ i : ℕ, l i) =
      (∑ᶠ i : ℕ, f i) - epsilon r • ((∑ᶠ i : ℕ, e i) + (∑ᶠ i : ℕ, o i)) := by
    have sum_s : (∑ᶠ i : ℕ, s i) =
        (∑ᶠ i : ℕ, f i) - epsilon r • ((∑ᶠ i : ℕ, e i) + (∑ᶠ i : ℕ, o i)) := by
      dsimp only [s]
      have subtract := finsum_sub_distrib hf ((he.add ho).smul_right (fun _ => epsilon r))
      change (∑ᶠ i : ℕ, (f i - epsilon r • (e i + o i))) =
        (∑ᶠ i : ℕ, f i) - (∑ᶠ i : ℕ, (epsilon r • (e i + o i))) at subtract
      rw [subtract]
      have factor := smul_finsum' (epsilon r) (he.add ho)
      change epsilon r • (∑ᶠ i : ℕ, (e i + o i)) =
        (∑ᶠ i : ℕ, (epsilon r • (e i + o i))) at factor
      rw [← factor, finsum_add_distrib he ho]
    rw [← sum_s]
    apply (cycles D H).injective_subtype
    rw [map_finsum _ hl, map_finsum _ hs]
    exact original_equality
  have hx0 : (2 : ℂ)⁻¹ •
      (classOf D H h26 hHG hGH x + parity D H h26 hHG hGH (classOf D H h26 hHG hGH x)) =
        classOf D H h26 hHG hGH x0 := by
    simp only [x0, map_smul, map_add, parity_classOf]
  have hx1 : (2 : ℂ)⁻¹ •
      (classOf D H h26 hHG hGH x - parity D H h26 hHG hGH (classOf D H h26 hHG hGH x)) =
        classOf D H h26 hHG hGH x1 := by
    simp only [x1, map_smul, map_sub, parity_classOf]
  have ql : jacobiLeft D H h26 hHG hGH
      (classOf D H h26 hHG hGH x) (classOf D H h26 hHG hGH y)
      (classOf D H h26 hHG hGH z) p q r =
        fun i => classOf D H h26 hHG hGH (l i) := by
    funext i
    simp only [jacobiLeft, l, mode_classOf, map_smul]
  have qf : jacobiForward D H h26 hHG hGH
      (classOf D H h26 hHG hGH x) (classOf D H h26 hHG hGH y)
      (classOf D H h26 hHG hGH z) p q r =
        fun i => classOf D H h26 hHG hGH (f i) := by
    funext i
    simp only [jacobiForward, f, w, mode_classOf, map_smul]
  have qe : jacobiReverseEven D H h26 hHG hGH
      (classOf D H h26 hHG hGH x) (classOf D H h26 hHG hGH y)
      (classOf D H h26 hHG hGH z) p q r =
        fun i => classOf D H h26 hHG hGH (e i) := by
    funext i
    simp only [jacobiReverseEven, hx0, e, w, mode_classOf, map_smul]
  have qo : jacobiReverseOdd D H h26 hHG hGH
      (classOf D H h26 hHG hGH x) (classOf D H h26 hHG hGH y)
      (classOf D H h26 hHG hGH z) p q r =
        fun i => classOf D H h26 hHG hGH (o i) := by
    funext i
    dsimp only [jacobiReverseOdd]
    rw [hx1, parity_classOf]
    simp only [o, w, mode_classOf, map_smul]
  rw [ql, qf, qe, qo]
  refine ⟨hl.fun_comp (map_zero (classOf D H h26 hHG hGH)),
    hf.fun_comp (map_zero (classOf D H h26 hHG hGH)),
    he.fun_comp (map_zero (classOf D H h26 hHG hGH)),
    ho.fun_comp (map_zero (classOf D H h26 hHG hGH)), ?_⟩
  have result := congrArg (classOf D H h26 hHG hGH) cycle_equality
  rw [map_finsum _ hl, map_sub, map_smul, map_add,
    map_finsum _ hf, map_finsum _ he, map_finsum _ ho] at result
  exact result

set_option maxHeartbeats 1000000 in
-- The supported derivative coefficient reductions exceeded 200000 in the native build.
/-- State translation differentiates the descended field. This additional
translation law consumes the quotient all-integer Borcherds theorem above.
The scalar negative-binomial identity is reused from the original lattice
derivative supplier, with its attribution; it is not reproved here. -/
theorem state_derivative_modes (a : Cohomology D H h26 hHG hGH) (n : ℤ) :
    ((Y D H h26 hHG hGH (translation D H h26 hHG hGH a))[[n]]) =
      -(n : ℂ) • ((Y D H h26 hHG hGH a)[[n - 1]]) := by
  classical
  apply LinearMap.ext; intro c
  simp only [Y_modes, LinearMap.smul_apply]
  let vac := vacuum D H h26 hHG hGH
  let a0 := (2 : ℂ)⁻¹ • (a + parity D H h26 hHG hGH a)
  let a1 := (2 : ℂ)⁻¹ • (a - parity D H h26 hHG hGH a)
  have split : a0 + a1 = a := by dsimp [a0, a1]; module
  have weight (i : ℕ) : (-1 : ℂ)^i * integerBinomial (-2) i = (i + 1 : ℂ) := by
    simpa only [integerBinomial] using minus_two_weight i
  let left : ℕ → Cohomology D H h26 hHG hGH := fun i =>
    (i + 1 : ℂ) • mode D H h26 hHG hGH (-2 - i) a
      (mode D H h26 hHG hGH (n + i) vac c)
  let right : ℕ → Cohomology D H h26 hHG hGH := fun i =>
    (i + 1 : ℂ) • mode D H h26 hHG hGH (n + (-2) - i) vac
      (mode D H h26 hHG hGH i a c)
  have src := borcherds D H h26 hHG hGH a vac c 0 n (-2)
  have lsum : (∑ᶠ i : ℕ, jacobiLeft D H h26 hHG hGH a vac c 0 n (-2) i) =
      mode D H h26 hHG hGH n (translation D H h26 hHG hGH a) c := by
    rw [finsum_eq_single _ 0]
    · simp [jacobiLeft, integerBinomial, translation_as_minusTwo, Y_modes, vac]
    · intro i hi
      simp [jacobiLeft, integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]
  have fsum : (∑ᶠ i : ℕ, jacobiForward D H h26 hHG hGH a vac c 0 n (-2) i) =
      ∑ᶠ i : ℕ, left i := by
    apply finsum_congr; intro i
    simp only [jacobiForward, zero_add, weight, left]
  have reverse (i : ℕ) :
      jacobiReverseEven D H h26 hHG hGH a vac c 0 n (-2) i +
        jacobiReverseOdd D H h26 hHG hGH a vac c 0 n (-2) i = right i := by
    change
      (((-1 : ℂ)^i) * integerBinomial (-2) i) •
          mode D H h26 hHG hGH (n + (-2) - i) vac
            (mode D H h26 hHG hGH (0 + i) a0 c) +
        (((-1 : ℂ)^i) * integerBinomial (-2) i) •
          mode D H h26 hHG hGH (n + (-2) - i)
            (parity D H h26 hHG hGH vac)
            (mode D H h26 hHG hGH (0 + i) a1 c) = _
    rw [show parity D H h26 hHG hGH vac = vac from parity_vacuum D H h26 hHG hGH]
    simp only [weight, zero_add]
    rw [← smul_add, ← map_add, ← LinearMap.add_apply, ← map_add, split]
  have rsum :
      (∑ᶠ i : ℕ, jacobiReverseEven D H h26 hHG hGH a vac c 0 n (-2) i) +
        (∑ᶠ i : ℕ, jacobiReverseOdd D H h26 hHG hGH a vac c 0 n (-2) i) =
          ∑ᶠ i : ℕ, right i := by
    rw [← finsum_add_distrib src.2.2.1 src.2.2.2.1]
    exact finsum_congr reverse
  have h := src.2.2.2.2
  rw [lsum, fsum, rsum, show epsilon (-2) = 1 by norm_num [epsilon], one_smul] at h
  rcases lt_trichotomy n 0 with hn | hn | hn
  · have rz : ∀ i : ℕ, right i = 0 := by
      intro i
      simp [right, vac, vacuum_mode, show n + (-2) - (i : ℤ) ≠ -1 by omega]
    let j : ℕ := (-n - 1).toNat
    have index : n + (j : ℤ) = -1 := by dsimp [j]; omega
    have mindex : (-2 : ℤ) - j = n - 1 := by dsimp [j]; omega
    have scalar : (j + 1 : ℂ) = -(n : ℂ) := by
      exact_mod_cast (show (j : ℤ) + 1 = -n by dsimp [j]; omega)
    have lf : (∑ᶠ i : ℕ, left i) =
        -(n : ℂ) • mode D H h26 hHG hGH (n - 1) a c := by
      rw [finsum_eq_single _ j]
      · simp only [left, vac, vacuum_mode, if_pos index, mindex, scalar]
      · intro i hi
        simp [left, vac, vacuum_mode,
          show n + (i : ℤ) ≠ -1 by dsimp [j] at hi; omega]
    simpa only [rz, finsum_zero, sub_zero, lf] using h
  · subst n
    have lz : ∀ i : ℕ, left i = 0 := by
      intro i
      simp [left, vac, vacuum_mode, show (0 : ℤ) + i ≠ -1 by omega]
    have rz : ∀ i : ℕ, right i = 0 := by
      intro i
      dsimp only [right, vac]
      rw [vacuum_mode, if_neg (show (0 : ℤ) + (-2) - i ≠ -1 by omega), smul_zero]
    simpa only [lz, rz, finsum_zero, sub_self, Int.cast_zero,
      neg_zero, zero_smul] using h
  · have lz : ∀ i : ℕ, left i = 0 := by
      intro i
      simp [left, vac, vacuum_mode, show n + (i : ℤ) ≠ -1 by omega]
    let j : ℕ := (n - 1).toNat
    have index : n + (-2) - (j : ℤ) = -1 := by dsimp [j]; omega
    have mindex : (j : ℤ) = n - 1 := by dsimp [j]; omega
    have scalar : (j + 1 : ℂ) = (n : ℂ) := by
      exact_mod_cast (show (j : ℤ) + 1 = n by dsimp [j]; omega)
    have rf : (∑ᶠ i : ℕ, right i) =
        (n : ℂ) • mode D H h26 hHG hGH (n - 1) a c := by
      rw [finsum_eq_single _ j]
      · dsimp only [right, vac]
        rw [vacuum_mode, if_pos index, mindex, scalar]
      · intro i hi
        simp [right, vac, vacuum_mode,
          show n + (-2) - (i : ℤ) ≠ -1 by dsimp [j] at hi; omega]
    simpa only [lz, finsum_zero, zero_sub, rf, neg_smul] using h

private theorem derivative_one_modes
    (A : VertexOperator ℂ (Cohomology D H h26 hHG hGH)) (n : ℤ) :
    ((dividedDerivative 1 A)[[n]]) = -(n : ℂ) • (A[[n - 1]]) := by
  apply LinearMap.ext; intro x
  change Ring.choose (-n - 1 + 1) 1 • HVertexOperator.coeff A (-n - 1 + 1) x = _
  rw [Ring.choose_one_right, VertexOperator.coeff_eq_ncoeff,
    show -(-n - 1 + 1) - 1 = n - 1 by omega, ← Int.cast_smul_eq_zsmul ℂ]
  simp only [sub_add_cancel, Int.cast_neg, LinearMap.smul_apply]

theorem state_derivative (a : Cohomology D H h26 hHG hGH) :
    Y D H h26 hHG hGH (translation D H h26 hHG hGH a) =
      dividedDerivative 1 (Y D H h26 hHG hGH a) := by
  apply HVertexOperator.coeff_inj (Γ := ℤ) (R := ℂ)
    (V := Cohomology D H h26 hHG hGH) (W := Cohomology D H h26 hHG hGH)
  funext power
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff,
    state_derivative_modes, derivative_one_modes]

end
end D5.S3.VertexAlgebra.LatticeBRSTCohomologyField
