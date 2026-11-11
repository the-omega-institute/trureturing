/- GID: D5/S3/VertexAlgebra/Sectors/LatticeCosetWeakAssociativity
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeCosetWeakAssociativity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual rectangular numerator support, inverse reconstruction and ordinary uniqueness. -/

/-
Delivery metadata: source-only semantic assessment, not a machine verdict.
proof_shape: recover_iterate, actual_shared_numerator: content after inlining
the supplied consumed helper chain (semantic assessment, not a machine verdict).
escape_witness: Actual rectangular support before coordinate identification,
finite inverse binomial transforms, ordinary shear inverse and negative-coordinate
boundary checks reconstruct both actual coefficient families. Uniqueness concerns
the ordinary H array. It is not a stand-alone conjunction of supplied conclusions.
consumed bind-only helper: shifted_equal -> shifted_rectangular and
iterateShift_eq_extend. The genuine content is the support/inverse/coordinate
chain; generic interfaces and thin applications provide no escape witness.
admission_basis: escape-witness (proposed; no current acceptance claimed).
utility: none. General exact identities on infinite dependent families; finite
coefficient sums are not a finite catalogue or a positive bounded instance.
Attribution: supplied original source and its unchanged charged convolution
supplier; Bakalov--Kac math/0602072 Theorem 3.5, Corollary 3.5 (23), section 3.6
(27); prerequisite math/0402315v1 and native attributions remain unchanged.

Both modules: preserve every original signature/quantifier, finite rank zero,
arbitrary integral B, symmetric even C, all original finite charge/oscillator
states, all signed modes/cutoffs, positive ORIGINAL G only, full Schur and
original epsilon. No analytic sewing, actual quotient F/exchange, scalar
polynomiality, categorical realization, string/AdS completion or literature
novelty claim.

Delivery status: metadata entries above are the supplied proposals for final
integration, not an admission, mirror generation, waiver approval or freeze.
The exact preserved native source suffix has supplied compiled evidence.
This metadata-modified candidate still requires real final integration checks;
the supplied native receipts do not validate these changed file bytes.
-/

import D5.S3.VertexAlgebra.Sectors.LatticeCosetChargedJacobi
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Sum
import Batteries.Tactic.OpenPrivate

/-!
Actual charged weak associativity and its ordinary shared numerator, on all
original lattice states. Only the ORIGINAL Gram form is positive definite.
The symmetric even external block may be singular or indefinite, and both
ranks may be zero. No uniform outer-field truncation is assumed.

Reference: Bakalov--Kac, Generalized vertex algebras, math/0602072,
Theorem 3.5, Corollary 3.5 (23), and section 3.6 (27). The older
math/0402315 lattice-construction citations in the prerequisite are unchanged.

The coefficient space below is the transparent type Nat -> Nat -> V, i.e.
ordinary two-variable V-valued power series. It needs only a complex module.
Mathlib's ring-valued substitution API is not imposed on the actual Carrier.
All coordinate sums are finite total-degree sums, not iterated-Hahn limits.
The private binomial convolution is REUSED from the unchanged prerequisite.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeCosetWeakAssociativity

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeAllStateField
open LatticeSugawaraConformal LatticeSugawaraCurrents LatticeDiscriminantTheta
open LatticeCosetCompression LatticeCosetChargedJacobi Matrix
open scoped BigOperators VertexOperator

noncomputable section

open private binomial_convolution from
  D5.S3.VertexAlgebra.Sectors.LatticeCosetChargedJacobi

private theorem finite_sum_of_tail {V : Type*} [AddCommGroup V]
    (f : ℕ → V) (n : ℕ) (tail : ∀ i, n ≤ i → f i = 0) :
    (∑ᶠ i : ℕ, f i) = ∑ i ∈ Finset.range n, f i := by
  classical
  apply finsum_eq_sum_of_support_subset
  intro i hi
  apply Finset.mem_range.mpr
  by_contra hn
  exact hi (tail i (by omega))

/- The joint bound exists BEFORE any interchange. This is precisely the
triangle i+j <= e; Finset.sum_range_diag_flip is the existing reindexer. -/
private theorem finite_triangle {V : Type*} [AddCommGroup V]
    (f : ℕ → ℕ → V) (e : ℕ) :
    (∑ i ∈ Finset.range (e+1), ∑ j ∈ Finset.range (e-i+1), f i j) =
      ∑ k ∈ Finset.range (e+1), ∑ i ∈ Finset.range (k+1), f i (k-i) := by
  symm
  convert Finset.sum_range_diag_flip (e+1) f using 1
  apply Finset.sum_congr rfl
  intro i hi
  have := Finset.mem_range.mp hi
  rw [show e+1-i = e-i+1 by omega]

/-- Ordinary linear change of variables t = x + z*y on nonnegative powers.
It is defined by its finite coefficient formula, on the actual module. -/
def coordinateChange {V : Type*} [AddCommGroup V] [Module ℂ V]
    (z : ℂ) : (ℕ → ℕ → V) →ₗ[ℂ] (ℕ → ℕ → V) where
  toFun F d e := ∑ j ∈ Finset.range (e+1),
    (z^j * ((d+j).choose j : ℂ)) • F (d+j) (e-j)
  map_add' F G := by
    funext d e
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' q F := by
    funext d e
    simp only [Pi.smul_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact smul_comm _ _ _

private theorem coordinateChange_apply {V : Type*} [AddCommGroup V] [Module ℂ V]
    (z : ℂ) (F : ℕ → ℕ → V) (d e : ℕ) :
    coordinateChange z F d e = ∑ j ∈ Finset.range (e+1),
      (z^j * ((d+j).choose j : ℂ)) • F (d+j) (e-j) := rfl

private theorem coordinate_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : ℕ → ℕ → V) (d e : ℕ) : coordinateChange 0 F d e = F d e := by
  classical
  rw [coordinateChange_apply, Finset.sum_eq_single 0]
  · simp
  · intro j hj hne
    simp [zero_pow hne]
  · simp

private theorem choose_triangle (d i j : ℕ) :
    ((d+i).choose i : ℂ) * ((d+i+j).choose j : ℂ) =
      ((d+(i+j)).choose (i+j) : ℂ) * ((i+j).choose i : ℂ) := by
  have hc := Nat.choose_mul (n := d+i+j) (k := i+j) (s := j) (by omega)
  rw [show d+i+j-j = d+i by omega, show i+j-j = i by omega,
    ← Nat.choose_symm_add (a := i) (b := j)] at hc
  have hc' := congrArg (fun n : ℕ => (n : ℂ)) hc
  push_cast at hc'
  simpa [Nat.add_assoc, mul_comm] using hc'.symm

/- This is the substantive ordinary inverse, not an inverse supplied as a
premise. The only inputs are the finite triangle, choose_mul and add_pow. -/
private theorem coordinate_add {V : Type*} [AddCommGroup V] [Module ℂ V]
    (z q : ℂ) (F : ℕ → ℕ → V) (d e : ℕ) :
    coordinateChange z (coordinateChange q F) d e =
      coordinateChange (z+q) F d e := by
  classical
  calc
    _ = ∑ i ∈ Finset.range (e+1), ∑ j ∈ Finset.range (e-i+1),
        ((z^i * ((d+i).choose i : ℂ)) *
          (q^j * ((d+i+j).choose j : ℂ))) • F (d+i+j) (e-i-j) := by
      simp only [coordinateChange_apply, Finset.smul_sum, smul_smul]
    _ = ∑ k ∈ Finset.range (e+1), ∑ i ∈ Finset.range (k+1),
        ((z^i * ((d+i).choose i : ℂ)) *
          (q^(k-i) * ((d+i+(k-i)).choose (k-i) : ℂ))) •
            F (d+i+(k-i)) (e-i-(k-i)) := finite_triangle _ e
    _ = ∑ k ∈ Finset.range (e+1),
        ((z+q)^k * ((d+k).choose k : ℂ)) • F (d+k) (e-k) := by
      apply Finset.sum_congr rfl
      intro k hk
      have ke : k ≤ e := by have := Finset.mem_range.mp hk; omega
      calc
        _ = ∑ i ∈ Finset.range (k+1),
            ((z^i * q^(k-i) * (k.choose i : ℂ)) * ((d+k).choose k : ℂ)) •
              F (d+k) (e-k) := by
          apply Finset.sum_congr rfl
          intro i hi
          have ik : i ≤ k := by have := Finset.mem_range.mp hi; omega
          have factor := choose_triangle d i (k-i)
          rw [show i+(k-i) = k by omega,
            show d+i+(k-i) = d+k by omega] at factor
          rw [show d+i+(k-i) = d+k by omega,
            show e-i-(k-i) = e-k by omega]
          congr 1
          calc
            _ = z^i * q^(k-i) *
                (((d+i).choose i : ℂ) * ((d+k).choose (k-i) : ℂ)) := by ring
            _ = _ := by rw [factor]; ring
        _ = _ := by rw [← Finset.sum_smul, ← Finset.sum_mul, ← add_pow]
    _ = _ := rfl

private theorem coordinate_inverse {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : ℕ → ℕ → V) (d e : ℕ) :
    coordinateChange 1 (coordinateChange (-1) F) d e = F d e := by
  rw [coordinate_add, show (1 : ℂ)+(-1) = 0 by ring, coordinate_zero]

/-- Zero extension of an ordinary module-valued power series. No fractional
or negative ordinary exponent is smuggled into coordinateChange. -/
def extend {V : Type*} [Zero V] (F : ℕ → ℕ → V) (d e : ℤ) : V :=
  if 0 ≤ d ∧ 0 ≤ e then F d.toNat e.toNat else 0

/- Extending an ordinary positive shear by zero is compatible with its
finite binomial formula even at NEGATIVE first coordinates. A term crossing
the boundary has a natural binomial with upper index smaller than its lower
index and hence vanishes. This boundary check is essential for high modes. -/
private theorem extended_coordinate {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : ℕ → ℕ → V) (d : ℤ) (e' : ℕ) :
    extend (coordinateChange 1 F) d e' =
      ∑ i ∈ Finset.range (e'+1),
        ((Ring.choose ((d+(i : ℤ) : ℤ) : ℚ) i : ℚ) : ℂ) •
          extend F (d+i) ((e' : ℤ)-i) := by
  classical
  by_cases hd : 0 ≤ d
  · have hdn : (d.toNat : ℤ) = d := Int.toNat_of_nonneg hd
    rw [extend, if_pos ⟨hd, by omega⟩]
    simp only [Int.toNat_natCast, coordinateChange_apply, one_pow, one_mul]
    apply Finset.sum_congr rfl
    intro i hi
    have ie : i ≤ e' := by have := Finset.mem_range.mp hi; omega
    have hdi : 0 ≤ d+(i : ℤ) := by omega
    have hei : 0 ≤ (e' : ℤ)-i := by omega
    have hdiN : (d+(i : ℤ)).toNat = d.toNat+i := by omega
    have heiN : ((e' : ℤ)-i).toNat = e'-i := by omega
    have cast_di : ((d+(i : ℤ) : ℤ) : ℚ) = (d.toNat+i : ℕ) := by
      exact_mod_cast (show d+(i : ℤ) = ((d.toNat+i : ℕ) : ℤ) by omega)
    rw [cast_di, Ring.choose_natCast, Rat.cast_natCast,
      extend, if_pos ⟨hdi,hei⟩, hdiN, heiN]
  · rw [extend, if_neg (by tauto)]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hdi : 0 ≤ d+(i : ℤ)
    · have hdN : ((d+(i : ℤ)).toNat : ℤ) = d+(i : ℤ) :=
        Int.toNat_of_nonneg hdi
      have lt_i : (d+(i : ℤ)).toNat < i := by omega
      have cast_di : ((d+(i : ℤ) : ℤ) : ℚ) = ((d+(i : ℤ)).toNat : ℕ) := by
        exact_mod_cast hdN.symm
      rw [cast_di, Ring.choose_natCast, Nat.choose_eq_zero_of_lt lt_i]
      simp
    · rw [extend, if_neg (by tauto), smul_zero]

private theorem choose_reflection (h : ℚ) (k : ℕ) :
    ((Ring.choose (-h-1+(k : ℚ)) k : ℚ) : ℂ) =
      (-1 : ℂ)^k * ((Ring.choose h k : ℚ) : ℂ) := by
  have hQ := Ring.choose_neg (h+1-(k : ℚ)) k
  rw [show -(h+1-(k : ℚ)) = -h-1+(k : ℚ) by ring,
    show h+1-(k : ℚ)+(k : ℚ)-1 = h by ring] at hQ
  simp only [Units.smul_def, zsmul_eq_mul, Int.cast_negOnePow_natCast] at hQ
  exact_mod_cast hQ

/- Reexpress the inverse Laurent shear through the ORDINARY Psi. This proves
the product kernel iota_(x,y)(x-y)^h, including negative first coordinates;
the desired product identity is not a premise. Vandermonde is called, not
reproved. Both nested sums have the joint bound i+j <= e'. -/
private theorem coordinate_kernel {V : Type*} [AddCommGroup V] [Module ℂ V]
    (h : ℚ) (F : ℕ → ℕ → V) (d : ℤ) (e' : ℕ) :
    (∑ j ∈ Finset.range (e'+1),
      ((Ring.choose (-h-1-(d : ℚ)) j : ℚ) : ℂ) •
        extend (coordinateChange 1 F) (d+j) ((e' : ℤ)-j)) =
      ∑ k ∈ Finset.range (e'+1),
        ((-1 : ℂ)^k * ((Ring.choose h k : ℚ) : ℂ)) •
          extend F (d+k) ((e' : ℤ)-k) := by
  classical
  let x : ℚ := -h-1-(d : ℚ)
  have rows (j : ℕ) (hj : j ∈ Finset.range (e'+1)) :
      extend (coordinateChange 1 F) (d+j) ((e' : ℤ)-j) =
        ∑ i ∈ Finset.range (e'-j+1),
          ((Ring.choose ((d+(j+i : ℕ) : ℤ) : ℚ) i : ℚ) : ℂ) •
            extend F (d+(j+i : ℕ)) ((e' : ℤ)-(j+i : ℕ)) := by
    have je : j ≤ e' := by have := Finset.mem_range.mp hj; omega
    rw [show (e' : ℤ)-(j : ℤ) = ((e'-j : ℕ) : ℤ) by omega,
      extended_coordinate F (d+j) (e'-j)]
    apply Finset.sum_congr rfl
    intro i hi
    have first_index : d+(j : ℤ)+(i : ℤ) = d+((j+i : ℕ) : ℤ) := by
      push_cast
      omega
    have second_index : ((e'-j : ℕ) : ℤ)-(i : ℤ) =
        (e' : ℤ)-((j+i : ℕ) : ℤ) := by omega
    rw [first_index, second_index]
  calc
    _ = ∑ j ∈ Finset.range (e'+1), ∑ i ∈ Finset.range (e'-j+1),
        (((Ring.choose x j : ℚ) : ℂ) *
          ((Ring.choose ((d+(j+i : ℕ) : ℤ) : ℚ) i : ℚ) : ℂ)) •
            extend F (d+(j+i : ℕ)) ((e' : ℤ)-(j+i : ℕ)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [rows j hj, Finset.smul_sum]
      simp only [smul_smul, x]
    _ = ∑ k ∈ Finset.range (e'+1), ∑ j ∈ Finset.range (k+1),
        (((Ring.choose x j : ℚ) : ℂ) *
          ((Ring.choose ((d+(j+(k-j) : ℕ) : ℤ) : ℚ) (k-j) : ℚ) : ℂ)) •
            extend F (d+(j+(k-j) : ℕ)) ((e' : ℤ)-(j+(k-j) : ℕ)) :=
      finite_triangle _ e'
    _ = ∑ k ∈ Finset.range (e'+1),
        ((Ring.choose (x+((d+(k : ℤ) : ℤ) : ℚ)) k : ℚ) : ℂ) •
          extend F (d+k) ((e' : ℤ)-k) := by
      apply Finset.sum_congr rfl
      intro k hk
      have vandermonde :
          (∑ j ∈ Finset.range (k+1),
            ((Ring.choose x j : ℚ) : ℂ) *
              ((Ring.choose ((d+(k : ℤ) : ℤ) : ℚ) (k-j) : ℚ) : ℂ)) =
            ((Ring.choose (x+((d+(k : ℤ) : ℤ) : ℚ)) k : ℚ) : ℂ) := by
        have hv := Ring.add_choose_eq (r := x) (s := ((d+(k : ℤ) : ℤ) : ℚ)) k
          (Commute.all _ _)
        rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hv
        exact_mod_cast hv.symm
      calc
        _ = ∑ j ∈ Finset.range (k+1),
            (((Ring.choose x j : ℚ) : ℂ) *
              ((Ring.choose ((d+(k : ℤ) : ℤ) : ℚ) (k-j) : ℚ) : ℂ)) •
                extend F (d+k) ((e' : ℤ)-k) := by
          apply Finset.sum_congr rfl
          intro j hj
          have jk : j ≤ k := by have := Finset.mem_range.mp hj; omega
          rw [show j+(k-j) = k by omega]
        _ = _ := by rw [← Finset.sum_smul, vandermonde]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      have exponent : x+((d+(k : ℤ) : ℤ) : ℚ) = -h-1+(k : ℚ) := by
        dsimp only [x]
        push_cast
        ring
      rw [exponent, choose_reflection]

variable (D : LatticeData) {e : ℕ}
variable (B : Matrix (Fin D.rank) (Fin e) ℤ) (C : Matrix (Fin e) (Fin e) ℤ)
variable (hC : ∀ i j, C i j = C j i) (hCe : ∀ i, Even (C i i))

local notation "I" => compressed D B C hC hCe
local notation "S" => schur D B C

/-- The actual product coefficient, with the original injection, projection,
cocycle and all-state field unchanged. -/
def productCoefficient (a b c : Fin e → ℤ) (u v w : Carrier D) (m n : ℤ) : Carrier D :=
  I a (b+c) u m (I b c v n w)

/-- The actual iterate coefficient. The intermediate state is the actual
compressed inner mode, not an arbitrarily prescribed coherent family. -/
def iterateCoefficient (a b c : Fin e → ℤ) (u v w : Carrier D) (m n : ℤ) : Carrier D :=
  I (a+b) c (I a b u m v) n w

/-- sigma_plus of x^(N-beta) times the product: expand x=t+y in y/t.
Its coefficient at t^(alpha-r-1)y^(gamma-s-1). -/
def productShift (a b c : Fin e → ℤ) (u v w : Carrier D) (N r s : ℤ) : Carrier D :=
  ∑ᶠ i : ℕ, ((-1 : ℂ)^i * ((Ring.choose ((r : ℚ)+S a b) i : ℚ) : ℂ)) •
    productCoefficient D B C hC hCe a b c u v w (N+r-i) (s+i)

/-- iota_(y,t)(t+y)^(N-beta) times the iterate: expand in t/y.
This definition records the direction; equality is subsequently proved. -/
def iterateShift (a b c : Fin e → ℤ) (u v w : Carrier D) (N r s : ℤ) : Carrier D :=
  ∑ᶠ i : ℕ, ((Ring.choose ((N : ℚ)+S a c) i : ℚ) : ℂ) •
    iterateCoefficient D B C hC hCe a b c u v w (r+i) (N+s-i)

variable (a b c : Fin e → ℤ) (u v w : Carrier D)

private theorem product_high (M : ℤ)
    (hM : ∀ n : ℤ, M ≤ n → I b c v n w = 0) (m n : ℤ) (hn : M ≤ n) :
    productCoefficient D B C hC hCe a b c u v w m n = 0 := by
  simp only [productCoefficient, hM n hn, map_zero]

private theorem iterate_high (R : ℤ)
    (hR : ∀ m : ℤ, R ≤ m → I a b u m v = 0) (m n : ℤ) (hm : R ≤ m) :
    iterateCoefficient D B C hC hCe a b c u v w m n = 0 := by
  rw [iterateCoefficient, hR m hm]
  simp [compressed]

private theorem productShift_range (M N r s : ℤ)
    (hM : ∀ n : ℤ, M ≤ n → I b c v n w = 0) :
    productShift D B C hC hCe a b c u v w N r s =
      ∑ i ∈ Finset.range (M-s).toNat,
        ((-1 : ℂ)^i * ((Ring.choose ((r : ℚ)+S a b) i : ℚ) : ℂ)) •
          productCoefficient D B C hC hCe a b c u v w (N+r-i) (s+i) := by
  apply finite_sum_of_tail
  intro i hi
  rw [product_high D B C hC hCe a b c u v w M hM _ _ (by omega), smul_zero]

private theorem iterateShift_range (R N r s : ℤ)
    (hR : ∀ m : ℤ, R ≤ m → I a b u m v = 0) :
    iterateShift D B C hC hCe a b c u v w N r s =
      ∑ i ∈ Finset.range (R-r).toNat,
        ((Ring.choose ((N : ℚ)+S a c) i : ℚ) : ℂ) •
          iterateCoefficient D B C hC hCe a b c u v w (r+i) (N+s-i) := by
  apply finite_sum_of_tail
  intro i hi
  rw [iterate_high D B C hC hCe a b c u v w R hR _ _ (by omega), smul_zero]

/- A consumed p=N application. This is not the delivered mathematical
increment: rectangular support, inverse convolutions and coordinates follow. -/
private theorem shifted_equal (hD : (gramReal D).PosDef) (N : ℤ)
    (hN : ∀ p : ℤ, N ≤ p → I a c u p w = 0) (r s : ℤ) :
    productShift D B C hC hCe a b c u v w N r s =
      iterateShift D B C hC hCe a b c u v w N r s := by
  have hj := charged_borcherds D B C hC hCe hD a b c u v w N r s
  have reverse_zero : (∑ᶠ i : ℕ,
      ((-1 : ℂ)^i * ((Ring.choose ((r : ℚ)+S a b) i : ℚ) : ℂ)) •
        I b (a+c) v (r+s-i) (I a c u (N+i) w)) = 0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro i
    rw [hN (N+i) (by omega), map_zero, smul_zero]
  rw [reverse_zero, smul_zero, sub_zero] at hj
  exact hj.symm

private theorem shifted_rectangular (hD : (gramReal D).PosDef) (R M N : ℤ)
    (hR : ∀ m : ℤ, R ≤ m → I a b u m v = 0)
    (hM : ∀ n : ℤ, M ≤ n → I b c v n w = 0)
    (hN : ∀ p : ℤ, N ≤ p → I a c u p w = 0) (r s : ℤ) :
    (R ≤ r ∨ M ≤ s) →
      productShift D B C hC hCe a b c u v w N r s = 0 := by
  rintro (hr | hs)
  · rw [shifted_equal D B C hC hCe a b c u v w hD N hN,
      iterateShift_range D B C hC hCe a b c u v w R N r s hR]
    have hz : (R-r).toNat = 0 := by omega
    simp [hz]
  · rw [productShift_range D B C hC hCe a b c u v w M N r s hM]
    have hz : (M-s).toNat = 0 := by omega
    simp [hz]

/-- The actual ordinary numerator H, constructed from the actual product.
The index i runs only to e; no outer cutoff over intermediate states occurs. -/
def numerator (R M N : ℤ) (d e' : ℕ) : Carrier D :=
  ∑ i ∈ Finset.range (e'+1),
    ((-1 : ℂ)^i * ((Ring.choose (((R-1-(d : ℤ) : ℤ) : ℚ)+S a b) i : ℚ) : ℂ)) •
      productCoefficient D B C hC hCe a b c u v w
        (N+R-1-d-i) (M-1-e'+i)

/-- Psi(x,y) = H(x-y,y), defined on nonnegative ordinary coefficients. -/
def sharedNumerator (R M N : ℤ) : ℕ → ℕ → Carrier D :=
  coordinateChange (-1) (numerator D B C hC hCe a b c u v w R M N)

private theorem numerator_eq_productShift (R M N : ℤ)
    (hM : ∀ n : ℤ, M ≤ n → I b c v n w = 0) (d e' : ℕ) :
    numerator D B C hC hCe a b c u v w R M N d e' =
      productShift D B C hC hCe a b c u v w N (R-1-d) (M-1-e') := by
  unfold numerator
  rw [productShift_range D B C hC hCe a b c u v w M N _ _ hM]
  have hi : (M-(M-1-(e' : ℤ))).toNat = e'+1 := by omega
  rw [hi]
  apply Finset.sum_congr rfl
  intro i hi
  congr 2 <;> omega

private theorem productShift_eq_extend (hD : (gramReal D).PosDef) (R M N : ℤ)
    (hR : ∀ m : ℤ, R ≤ m → I a b u m v = 0)
    (hM : ∀ n : ℤ, M ≤ n → I b c v n w = 0)
    (hN : ∀ p : ℤ, N ≤ p → I a c u p w = 0) (r s : ℤ) :
    productShift D B C hC hCe a b c u v w N r s =
      extend (numerator D B C hC hCe a b c u v w R M N) (R-1-r) (M-1-s) := by
  classical
  by_cases hd : 0 ≤ R-1-r
  · by_cases he : 0 ≤ M-1-s
    · rw [extend, if_pos ⟨hd,he⟩,
        numerator_eq_productShift D B C hC hCe a b c u v w R M N hM]
      congr 1 <;> omega
    · rw [extend, if_neg (by tauto)]
      exact shifted_rectangular D B C hC hCe a b c u v w hD R M N hR hM hN r s
        (Or.inr (by omega))
  · rw [extend, if_neg (by tauto)]
    exact shifted_rectangular D B C hC hCe a b c u v w hD R M N hR hM hN r s
      (Or.inl (by omega))

private theorem iterateShift_eq_extend (hD : (gramReal D).PosDef) (R M N : ℤ)
    (hR : ∀ m : ℤ, R ≤ m → I a b u m v = 0)
    (hM : ∀ n : ℤ, M ≤ n → I b c v n w = 0)
    (hN : ∀ p : ℤ, N ≤ p → I a c u p w = 0) (r s : ℤ) :
    iterateShift D B C hC hCe a b c u v w N r s =
      extend (numerator D B C hC hCe a b c u v w R M N) (R-1-r) (M-1-s) := by
  rw [← shifted_equal D B C hC hCe a b c u v w hD N hN]
  exact productShift_eq_extend D B C hC hCe a b c u v w hD R M N hR hM hN r s

/- The reused convolution establishes the genuine inverse on the ACTUAL
iterate. f(k) already vanishes for k >= (R-m).toNat, so the supplier's
joint triangular cutoff is available before its finsum_curry step. -/
private theorem iterate_inverse (R N m n : ℤ)
    (hR : ∀ m : ℤ, R ≤ m → I a b u m v = 0) :
    (∑ᶠ j : ℕ, ((Ring.choose (-S a c-(N : ℚ)) j : ℚ) : ℂ) •
      iterateShift D B C hC hCe a b c u v w N (m+j) (n-N-j)) =
        iterateCoefficient D B C hC hCe a b c u v w m n := by
  classical
  let x : ℚ := (N : ℚ)+S a c
  let f : ℕ → Carrier D := fun k =>
    iterateCoefficient D B C hC hCe a b c u v w (m+k) (n-k)
  have cutoff : ∃ K : ℕ, ∀ k : ℕ, K ≤ k → f k = 0 := by
    refine ⟨(R-m).toNat, fun k hk => ?_⟩
    exact iterate_high D B C hC hCe a b c u v w R hR _ _ (by omega)
  have inverse_exponent : -S a c-(N : ℚ) = -x := by dsimp [x]; ring
  rw [inverse_exponent]
  calc
    _ = ∑ᶠ j : ℕ, ((Ring.choose (-x) j : ℚ) : ℂ) •
        (∑ᶠ i : ℕ, ((Ring.choose x i : ℚ) : ℂ) • f (j+i)) := by
      apply finsum_congr
      intro j
      apply congrArg (fun t : Carrier D => ((Ring.choose (-x) j : ℚ) : ℂ) • t)
      apply finsum_congr
      intro i
      dsimp only [iterateShift, f, x]
      congr 2 <;> push_cast <;> omega
    _ = ∑ᶠ k : ℕ, ((Ring.choose (0 : ℚ) k : ℚ) : ℂ) • f k := by
      simpa only [one_pow, one_mul, neg_add_cancel] using
        binomial_convolution (-x) x (1 : ℂ) f cutoff
    _ = f 0 := by
      rw [finsum_eq_single _ 0]
      · simp [Ring.choose_zero_right]
      · intro k hk
        rw [Ring.choose_zero_ite, if_neg hk]
        simp
    _ = _ := by simp [f]

/-- Every actual iterate mode is recovered from the finite product numerator.
Writing d=R-1-m, the range has d+1 terms when d>=0, and is empty when d<0.
In particular, the second numerator coordinate is N+M-1-n+j, with a PLUS j.
The second coordinate can be negative; extend then gives zero. -/
theorem recover_iterate (hD : (gramReal D).PosDef) (R M N : ℤ)
    (hR : ∀ m : ℤ, R ≤ m → I a b u m v = 0)
    (hM : ∀ n : ℤ, M ≤ n → I b c v n w = 0)
    (hN : ∀ p : ℤ, N ≤ p → I a c u p w = 0) (m n : ℤ) :
    iterateCoefficient D B C hC hCe a b c u v w m n =
      ∑ j ∈ Finset.range (R-m).toNat,
        ((Ring.choose (-S a c-(N : ℚ)) j : ℚ) : ℂ) •
          extend (numerator D B C hC hCe a b c u v w R M N)
            (R-1-m-j) (N+M-1-n+j) := by
  classical
  calc
    _ = ∑ᶠ j : ℕ, ((Ring.choose (-S a c-(N : ℚ)) j : ℚ) : ℂ) •
        iterateShift D B C hC hCe a b c u v w N (m+j) (n-N-j) :=
      (iterate_inverse D B C hC hCe a b c u v w R N m n hR).symm
    _ = ∑ j ∈ Finset.range (R-m).toNat,
        ((Ring.choose (-S a c-(N : ℚ)) j : ℚ) : ℂ) •
          iterateShift D B C hC hCe a b c u v w N (m+j) (n-N-j) := by
      apply finite_sum_of_tail
      intro j hj
      rw [iterateShift_range D B C hC hCe a b c u v w R N _ _ hR]
      have hz : (R-(m+(j : ℤ))).toNat = 0 := by omega
      simp [hz]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [iterateShift_eq_extend D B C hC hCe a b c u v w hD R M N hR hM hN]
      congr 2 <;> omega

/- Finite falling-binomial transport is used below to recover the product as
well. This is NOT a second Vandermonde proof: choose_smul_choose and add_pow
are consumed directly. The entire triangle is bounded before reindexing. -/
private theorem falling_inverse {V : Type*} [AddCommGroup V] [Module ℂ V]
    (x : ℚ) (f : ℕ → V) (e' : ℕ) :
    (∑ j ∈ Finset.range (e'+1), ((Ring.choose x j : ℚ) : ℂ) •
      (∑ i ∈ Finset.range (e'-j+1),
        ((-1 : ℂ)^i * ((Ring.choose (x-(j : ℚ)) i : ℚ) : ℂ)) • f (j+i))) = f 0 := by
  classical
  calc
    _ = ∑ j ∈ Finset.range (e'+1), ∑ i ∈ Finset.range (e'-j+1),
        (((Ring.choose x j : ℚ) : ℂ) *
          ((-1 : ℂ)^i * ((Ring.choose (x-(j : ℚ)) i : ℚ) : ℂ))) • f (j+i) := by
      simp only [Finset.smul_sum, smul_smul]
    _ = ∑ k ∈ Finset.range (e'+1), ∑ j ∈ Finset.range (k+1),
        (((Ring.choose x j : ℚ) : ℂ) *
          ((-1 : ℂ)^(k-j) * ((Ring.choose (x-(j : ℚ)) (k-j) : ℚ) : ℂ))) •
            f (j+(k-j)) := finite_triangle _ e'
    _ = ∑ k ∈ Finset.range (e'+1),
        (((1 : ℂ)+(-1))^k * ((Ring.choose x k : ℚ) : ℂ)) • f k := by
      apply Finset.sum_congr rfl
      intro k hk
      calc
        _ = ∑ j ∈ Finset.range (k+1),
            (((1 : ℂ)^j * (-1 : ℂ)^(k-j) * (k.choose j : ℂ)) *
              ((Ring.choose x k : ℚ) : ℂ)) • f k := by
          apply Finset.sum_congr rfl
          intro j hj
          have jk : j ≤ k := by have := Finset.mem_range.mp hj; omega
          have factorQ :
              Ring.choose x j * Ring.choose (x-(j : ℚ)) (k-j) =
                (k.choose j : ℚ) * Ring.choose x k := by
            simpa only [nsmul_eq_mul] using (Ring.choose_smul_choose x jk).symm
          have factor :
              ((Ring.choose x j : ℚ) : ℂ) *
                ((Ring.choose (x-(j : ℚ)) (k-j) : ℚ) : ℂ) =
                  (k.choose j : ℂ) * ((Ring.choose x k : ℚ) : ℂ) := by
            exact_mod_cast factorQ
          rw [show j+(k-j) = k by omega]
          congr 1
          simp only [one_pow, one_mul]
          calc
            _ = (-1 : ℂ)^(k-j) * (((Ring.choose x j : ℚ) : ℂ) *
                ((Ring.choose (x-(j : ℚ)) (k-j) : ℚ) : ℂ)) := by ring
            _ = _ := by rw [factor]; ring
        _ = _ := by rw [← Finset.sum_smul, ← Finset.sum_mul, ← add_pow]
    _ = f 0 := by
      rw [show (1 : ℂ)+(-1) = 0 by ring, Finset.sum_eq_single 0]
      · simp [Ring.choose_zero_right]
      · intro k hk hne
        simp [zero_pow hne]
      · simp

private theorem product_inverse (M N m n : ℤ)
    (hM : ∀ n : ℤ, M ≤ n → I b c v n w = 0) :
    productCoefficient D B C hC hCe a b c u v w m n =
      ∑ j ∈ Finset.range (M-n).toNat,
        ((Ring.choose (((m-N : ℤ) : ℚ)+S a b) j : ℚ) : ℂ) •
          productShift D B C hC hCe a b c u v w N (m-N-j) (n+j) := by
  classical
  by_cases hn : n < M
  · let E' : ℕ := (M-1-n).toNat
    have hE : (E' : ℤ) = M-1-n := Int.toNat_of_nonneg (by omega)
    have count : (M-n).toNat = E'+1 := by omega
    rw [count]
    let f : ℕ → Carrier D := fun k =>
      productCoefficient D B C hC hCe a b c u v w (m-k) (n+k)
    have rows (j : ℕ) (hj : j ∈ Finset.range (E'+1)) :
        productShift D B C hC hCe a b c u v w N (m-N-j) (n+j) =
          ∑ i ∈ Finset.range (E'-j+1),
            ((-1 : ℂ)^i * ((Ring.choose
              ((((m-N : ℤ) : ℚ)+S a b)-(j : ℚ)) i : ℚ) : ℂ)) • f (j+i) := by
      rw [productShift_range D B C hC hCe a b c u v w M N _ _ hM]
      have hj' := Finset.mem_range.mp hj
      have count' : (M-(n+(j : ℤ))).toNat = E'-j+1 := by omega
      rw [count']
      apply Finset.sum_congr rfl
      intro i hi
      have exponent : (((m-N-(j : ℤ) : ℤ) : ℚ)+S a b) =
          (((m-N : ℤ) : ℚ)+S a b)-(j : ℚ) := by push_cast; ring
      rw [exponent]
      dsimp only [f]
      congr 2 <;> push_cast <;> omega
    calc
      _ = f 0 := by simp [f]
      _ = _ := by
        symm
        calc
          _ = ∑ j ∈ Finset.range (E'+1),
              ((Ring.choose (((m-N : ℤ) : ℚ)+S a b) j : ℚ) : ℂ) •
                (∑ i ∈ Finset.range (E'-j+1),
                  ((-1 : ℂ)^i * ((Ring.choose
                    ((((m-N : ℤ) : ℚ)+S a b)-(j : ℚ)) i : ℚ) : ℂ)) • f (j+i)) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [rows j hj]
          _ = _ := falling_inverse _ f E'
  · rw [product_high D B C hC hCe a b c u v w M hM _ _ (by omega)]
    have count : (M-n).toNat = 0 := by omega
    simp [count]

private theorem recover_product (hD : (gramReal D).PosDef) (R M N : ℤ)
    (hR : ∀ m : ℤ, R ≤ m → I a b u m v = 0)
    (hM : ∀ n : ℤ, M ≤ n → I b c v n w = 0)
    (hN : ∀ p : ℤ, N ≤ p → I a c u p w = 0) (m n : ℤ) :
    productCoefficient D B C hC hCe a b c u v w m n =
      ∑ j ∈ Finset.range (M-n).toNat,
        ((Ring.choose (((m-N : ℤ) : ℚ)+S a b) j : ℚ) : ℂ) •
          extend (numerator D B C hC hCe a b c u v w R M N)
            (N+R-1-m+j) (M-1-n-j) := by
  rw [product_inverse D B C hC hCe a b c u v w M N m n hM]
  apply Finset.sum_congr rfl
  intro j hj
  rw [productShift_eq_extend D B C hC hCe a b c u v w hD R M N hR hM hN]
  congr 2 <;> omega

private theorem numerator_coordinates (R M N : ℤ) :
    coordinateChange 1 (sharedNumerator D B C hC hCe a b c u v w R M N) =
      numerator D B C hC hCe a b c u v w R M N := by
  funext d e'
  exact coordinate_inverse _ d e'

private theorem product_from_shared (hD : (gramReal D).PosDef) (R M N : ℤ)
    (hR : ∀ m : ℤ, R ≤ m → I a b u m v = 0)
    (hM : ∀ n : ℤ, M ≤ n → I b c v n w = 0)
    (hN : ∀ p : ℤ, N ≤ p → I a c u p w = 0) (m n : ℤ) :
    productCoefficient D B C hC hCe a b c u v w m n =
      ∑ j ∈ Finset.range (M-n).toNat,
        ((-1 : ℂ)^j * ((Ring.choose (-S a b-(R : ℚ)) j : ℚ) : ℂ)) •
          extend (sharedNumerator D B C hC hCe a b c u v w R M N)
            (N+R-1-m+j) (M-1-n-j) := by
  classical
  by_cases hn : n < M
  · let E' : ℕ := (M-1-n).toNat
    have hE : (E' : ℤ) = M-1-n := Int.toNat_of_nonneg (by omega)
    have count : (M-n).toNat = E'+1 := by omega
    calc
      _ = ∑ j ∈ Finset.range (M-n).toNat,
          ((Ring.choose (((m-N : ℤ) : ℚ)+S a b) j : ℚ) : ℂ) •
            extend (coordinateChange 1
              (sharedNumerator D B C hC hCe a b c u v w R M N))
                (N+R-1-m+j) (M-1-n-j) := by
        rw [numerator_coordinates]
        exact recover_product D B C hC hCe a b c u v w hD R M N hR hM hN m n
      _ = _ := by
        have hk := coordinate_kernel (-S a b-(R : ℚ))
          (sharedNumerator D B C hC hCe a b c u v w R M N) (N+R-1-m) E'
        have exponent : -(-S a b-(R : ℚ))-1-((N+R-1-m : ℤ) : ℚ) =
            (((m-N : ℤ) : ℚ)+S a b) := by push_cast; ring
        rw [exponent] at hk
        rw [count]
        convert hk using 1
        · apply Finset.sum_congr rfl
          intro j hj
          congr 2 <;> omega
        · apply Finset.sum_congr rfl
          intro j hj
          congr 2 <;> omega
  · rw [product_high D B C hC hCe a b c u v w M hM _ _ (by omega)]
    have count : (M-n).toNat = 0 := by omega
    simp [count]

/- Exact coefficient-level shared-numerator theorem. The two expansion maps
are evaluated on the actual original fields, and Psi is the explicit ordinary
series defined above. No arbitrary A/C families or coherence premises occur.

Put alpha=-S(a,b), beta=-S(a,c), gamma=-S(b,c). Then:
  productShift = [t^(alpha-r-1)y^(gamma-s-1)] sigma_plus(x^(N-beta) P_K),
  iterateShift = [t^(alpha-r-1)y^(gamma-s-1)]
                   iota_(y,t)(t+y)^(N-beta) A_K.
Their common zero-extended numerator is t^(alpha-R)y^(gamma-M) H(t,y).
The product formula below is exactly the coefficient expansion of
  x^(beta-N)y^(gamma-M) iota_(x,y)(x-y)^(alpha-R) Psi(x,y).
The iterate formula is exactly the expansion of
  t^(alpha-R)y^(gamma-M) iota_(y,t)(t+y)^(beta-N) Psi(t+y,y).

At C=0 these are the canonical Hahn fields with RAW rational q=-Schur,
K_ab(u)[m-q_ab]v=I_ab(u)[m]v. Bilinearity of Schur gives the shifts
alpha+beta and beta+gamma. q is not reduced modulo the integers.
sigma_plus expands x=t+y in y/t; the iterate multiplier expands in t/y.
Only after the rectangular-support proof do we identify the resulting
coefficient arrays in the common shifted quadrant. No equality between
incompatible iterated-Hahn domains is asserted. -/
theorem actual_shared_numerator (hD : (gramReal D).PosDef) (R M N : ℤ)
    (hR : ∀ m : ℤ, R ≤ m → I a b u m v = 0)
    (hM : ∀ n : ℤ, M ≤ n → I b c v n w = 0)
    (hN : ∀ p : ℤ, N ≤ p → I a c u p w = 0) :
    (∀ r s : ℤ,
      productShift D B C hC hCe a b c u v w N r s =
        extend (numerator D B C hC hCe a b c u v w R M N) (R-1-r) (M-1-s) ∧
      iterateShift D B C hC hCe a b c u v w N r s =
        extend (numerator D B C hC hCe a b c u v w R M N) (R-1-r) (M-1-s)) ∧
    (∀ d e' : ℕ,
      numerator D B C hC hCe a b c u v w R M N d e' =
        ∑ j ∈ Finset.range (e'+1), ((d+j).choose j : ℂ) •
          sharedNumerator D B C hC hCe a b c u v w R M N (d+j) (e'-j)) ∧
    (∀ m n : ℤ,
      productCoefficient D B C hC hCe a b c u v w m n =
        ∑ j ∈ Finset.range (M-n).toNat,
          ((-1 : ℂ)^j * ((Ring.choose (-S a b-(R : ℚ)) j : ℚ) : ℂ)) •
            extend (sharedNumerator D B C hC hCe a b c u v w R M N)
              (N+R-1-m+j) (M-1-n-j)) ∧
    (∀ m n : ℤ,
      iterateCoefficient D B C hC hCe a b c u v w m n =
        ∑ j ∈ Finset.range (R-m).toNat,
          ((Ring.choose (-S a c-(N : ℚ)) j : ℚ) : ℂ) •
            extend (coordinateChange 1
              (sharedNumerator D B C hC hCe a b c u v w R M N))
                (R-1-m-j) (N+M-1-n+j)) ∧
    (∃! F : ℕ → ℕ → Carrier D, ∀ r s : ℤ,
      productShift D B C hC hCe a b c u v w N r s =
        extend F (R-1-r) (M-1-s)) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r s
    exact ⟨productShift_eq_extend D B C hC hCe a b c u v w hD R M N hR hM hN r s,
      iterateShift_eq_extend D B C hC hCe a b c u v w hD R M N hR hM hN r s⟩
  · intro d e'
    have hc := congrFun (congrFun
      (numerator_coordinates D B C hC hCe a b c u v w R M N) d) e'
    simpa only [coordinateChange_apply, one_pow, one_mul] using hc.symm
  · intro m n
    exact product_from_shared D B C hC hCe a b c u v w hD R M N hR hM hN m n
  · intro m n
    rw [numerator_coordinates]
    exact recover_iterate D B C hC hCe a b c u v w hD R M N hR hM hN m n
  · refine ⟨numerator D B C hC hCe a b c u v w R M N, ?_, ?_⟩
    · intro r s
      exact productShift_eq_extend D B C hC hCe a b c u v w hD R M N hR hM hN r s
    · intro F hF
      funext d e'
      have hc := hF (R-1-(d : ℤ)) (M-1-(e' : ℤ))
      rw [← numerator_eq_productShift D B C hC hCe a b c u v w R M N hM d e',
        show R-1-(R-1-(d : ℤ)) = (d : ℤ) by omega,
        show M-1-(M-1-(e' : ℤ)) = (e' : ℤ) by omega] at hc
      simpa only [extend, Nat.cast_nonneg, and_self, if_true, Int.toNat_natCast] using hc.symm

/- The cutoff hypotheses above are actual statewise truncations. They exist
by compressed_high_modes with q=0: its natural K, coerced to Z, is a cutoff;
for m >= K use j=m.toNat and Int.toNat_of_nonneg to read back the native tail.
N uses only a,c,u,w. The theorem accepts EVERY integer cutoff satisfying the
three displayed tail conditions, including negative ones. The algebra never
needs an upper bound uniform over intermediate oscillator polynomials.

No analytic, fusion, anomaly, categorical, string or AdS completion is claimed.
-/

end
end D5.S3.VertexAlgebra.LatticeCosetWeakAssociativity


