/-
SOURCE-ONLY integer ghost-number/parity and bracket-degree consumer.

This is one source draft.  It keeps the supplied State, the supplied full
cycles/range quotient, Pg/Pi, fixed grade submodules, product, Delta = [b0 P0],
and the supplied parity-indexed bracket.  It does not introduce a carrier,
quotient, differential, cohomology, product, or generic BV library.  The
supplied files are terminally collected source drafts; no native elaboration,
kernel check, declaration report, or official acceptance is claimed here.

The occupation calculation uses the actual signed charge
  #(odd occupied) - #(even occupied)
from BcGhostCharge, and proves its sign agrees with the cardinality sign for
all integer exponents, including negative ghost number.  Bakalov--Kac,
Scott Carnahan / vertexAlg, Kalle Kytola, the original ghost suppliers, and
Mathlib retain the attribution carried by the imported sources.  No novelty
or parent-goal completion is asserted.
-/

import D5.S3.VertexAlgebra.Lattice.LatticeBRSTGhostNumberProduct
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTBVBracket
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTZeroEnergyParity
import Mathlib.Tactic.Module

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

open scoped BigOperators TensorProduct Classical

namespace D5.S3.VertexAlgebra.LatticeBRSTGhostNumberBracket

open LatticeGeneratingFieldLocality (LatticeData)
open LatticeSugawaraCurrents (gramComplex)
open LatticeMatterGhostCoupling (State)
open LatticeBRSTCohomologyField (Cohomology classOf classOf_surjective product)
open D5.S3.VertexAlgebra.LatticeBRSTZeroEnergyReduction
  (FullLabel fullBasis Delta)
open D5.S3.VertexAlgebra.LatticeBRSTGhostNumberGrading
  (labelCharge Pg Pg_basis Pi Pi_classOf grade mem_grade cyclePg cyclePg_val
    Delta_lowers_ghost_number)
open D5.S3.Quantum.Fermionic
open D5.S3.Quantum.Fermionic.CountableOccupationFock (Fock)
open D5.S3.Quantum.Fermionic.BcGhostCharge (charge)
open D5.S3.VertexAlgebra.LatticeBRSTZeroEnergyParity (parity_fullBasis)
open D5.S3.VertexAlgebra.LatticeBRSTGhostNumberProduct (product_mem_grade)
open D5.S3.VertexAlgebra.LatticeBRSTBVBracket
  (bracket bracket_apply bracket_parity bracket_leibniz bracket_antisymmetric
    bracket_delta bracket_jacobi)

noncomputable section

/-! The sign of a zpow depends only on the even class of its exponent. -/

private theorem neg_one_zpow_congr {a b : ℤ} (h : Even (a - b)) :
    (-1 : ℂ) ^ a = (-1 : ℂ) ^ b := by
  rcases h with ⟨t, ht⟩
  have hab : a = b + 2 * t := by omega
  rw [hab, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_mul]
  norm_num

private theorem neg_one_zpow_natAbs (k : ℤ) :
    (-1 : ℂ) ^ k = (-1 : ℂ) ^ k.natAbs := by
  cases k with
  | ofNat n => simp
  | negSucc n =>
      rw [zpow_negSucc]
      rw [← inv_pow]
      norm_num

private theorem sign_of_even_nat {n : ℕ} {z : ℤ} (h : Even ((n : ℤ) - z)) :
    (-1 : ℂ) ^ n = (-1 : ℂ) ^ z := by
  simpa only [zpow_natCast] using neg_one_zpow_congr h

/-! The actual charge/cardinality identity, before any state or quotient. -/

private theorem charge_card_difference (S : Finset ℕ) :
    Even (charge S - (S.card : ℤ)) := by
  classical
  have hpart := Finset.card_filter_add_card_filter_not
    (p := fun j : ℕ => j % 2 = 1) (s := S)
  have hfilter : S.filter (fun j => ¬ j % 2 = 1) =
      S.filter (fun j => j % 2 = 0) := by
    ext j
    simp only [Finset.mem_filter]
    constructor <;> intro h
    · exact ⟨h.1, by omega⟩
    · exact ⟨h.1, by omega⟩
  rw [hfilter] at hpart
  have hpartZ :
      ((S.filter (fun j => j % 2 = 1)).card : ℤ) +
        ((S.filter (fun j => j % 2 = 0)).card : ℤ) =
      (S.card : ℤ) := by
    exact_mod_cast hpart
  refine ⟨-((S.filter (fun j => j % 2 = 0)).card : ℤ), ?_⟩
  simp only [charge]
  omega

/-! The real signed occupation charge has the literal parity sign.  The
    right-hand side is a natural power only because occupation.card is
    nonnegative; the left-hand side is an unrestricted integer zpow. -/
theorem charge_sign_card (S : Finset ℕ) :
    (-1 : ℂ) ^ charge S = (-1 : ℂ) ^ S.card := by
  have hdiff : Even ((S.card : ℤ) - charge S) := by
    simpa only [neg_sub] using (charge_card_difference S).neg
  have h := sign_of_even_nat (n := S.card) (z := charge S)
    hdiff
  exact h.symm

/-! The raw parity/Pg identity on the supplied full State. -/

theorem state_parity_Pg (D : LatticeData) (k : ℤ) :
    LatticeMatterGhostStateField.parity D * Pg D k =
      (-1 : ℂ) ^ k • Pg D k := by
  apply (fullBasis D).ext
  intro label
  simp only [Module.End.mul_apply, LinearMap.smul_apply, Pg_basis, map_smul,
    parity_fullBasis]
  by_cases hk : labelCharge D label = k
  · simp only [if_pos hk, one_smul]
    rw [← hk]
    change (-1 : ℂ) ^ label.2.card • (fullBasis D) label =
      (-1 : ℂ) ^ charge label.2 • (fullBasis D) label
    rw [← charge_sign_card label.2]
  · simp only [if_neg hk, zero_smul, map_zero, smul_zero]

/-! Descent of the raw identity to the unchanged full quotient. -/

theorem parity_Pi
    (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1)
    (k : ℤ) (u : Cohomology D H h26 hHG hGH) :
    LatticeBRSTCohomologyField.parity D H h26 hHG hGH
        (Pi D H h26 hHG hGH k u) =
      (-1 : ℂ) ^ k • Pi D H h26 hHG hGH k u := by
  obtain ⟨x, rfl⟩ := classOf_surjective D H h26 hHG hGH u
  rw [Pi_classOf, LatticeBRSTCohomologyField.parity_classOf]
  apply congrArg (classOf D H h26 hHG hGH)
  apply Subtype.ext
  change LatticeMatterGhostStateField.parity D
      (Pg D k (x : State D)) =
    (-1 : ℂ) ^ k • Pg D k (x : State D)
  exact LinearMap.congr_fun (state_parity_Pg D k) (x : State D)

/-! Membership in the existing integer grade supplies the original quotient
    parity eigen-equation.  No parity-equals-charge-mod-two assumption is
    used: the equation is obtained by the actual Pg/Pi projection identity. -/
theorem grade_parity
    (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1)
    (k : ℤ) (u : Cohomology D H h26 hHG hGH)
    (hu : u ∈ grade D H h26 hHG hGH k) :
    LatticeBRSTCohomologyField.parity D H h26 hHG hGH u =
      (-1 : ℂ) ^ k • u := by
  have fixed := (mem_grade D H h26 hHG hGH k u).mp hu
  calc
    LatticeBRSTCohomologyField.parity D H h26 hHG hGH u =
        LatticeBRSTCohomologyField.parity D H h26 hHG hGH
          (Pi D H h26 hHG hGH k u) := by rw [fixed]
    _ = (-1 : ℂ) ^ k • Pi D H h26 hHG hGH k u := parity_Pi D H h26 hHG hGH k u
    _ = (-1 : ℂ) ^ k • u := by rw [fixed]

/-! Integer parity-label arithmetic used to specialize the supplied bracket. -/

private theorem even_natAbs_sub (k : ℤ) : Even ((k.natAbs : ℤ) - k) := by
  cases k with
  | ofNat n => simp
  | negSucc n =>
      have hnat : (Int.negSucc n).natAbs = n + 1 := by simp
      rw [hnat]
      refine ⟨n + 1, ?_⟩
      omega

private theorem even_sum_degree (k l : ℤ) :
    Even ((k.natAbs : ℤ) + (l.natAbs : ℤ) + 1 - (k + l - 1)) := by
  rcases even_natAbs_sub k with ⟨a, ha⟩
  rcases even_natAbs_sub l with ⟨b, hb⟩
  have hka : (k.natAbs : ℤ) = k + 2 * a := by omega
  have hlb : (l.natAbs : ℤ) = l + 2 * b := by omega
  refine ⟨a + b + 1, ?_⟩
  rw [hka, hlb]
  ring

private theorem even_delta_degree (k : ℤ) :
    Even ((k.natAbs : ℤ) + 1 - (k - 1)) := by
  rcases even_natAbs_sub k with ⟨a, ha⟩
  have hka : (k.natAbs : ℤ) = k + 2 * a := by omega
  refine ⟨a + 1, ?_⟩
  rw [hka]
  ring

private theorem even_leibniz_degree (k l : ℤ) :
    Even (((k.natAbs : ℤ) + 1) * (l.natAbs : ℤ) - (k - 1) * l) := by
  rcases even_natAbs_sub k with ⟨a, ha⟩
  rcases even_natAbs_sub l with ⟨b, hb⟩
  have hka : (k.natAbs : ℤ) = k + 2 * a := by omega
  have hlb : (l.natAbs : ℤ) = l + 2 * b := by omega
  refine ⟨l + b * (k + 1) + a * l + 2 * a * b, ?_⟩
  rw [hka, hlb]
  ring

private theorem even_jacobi_degree (k l : ℤ) :
    Even (((k.natAbs : ℤ) + 1) * ((l.natAbs : ℤ) + 1) -
      (k - 1) * (l - 1)) := by
  rcases even_natAbs_sub k with ⟨a, ha⟩
  rcases even_natAbs_sub l with ⟨b, hb⟩
  have hka : (k.natAbs : ℤ) = k + 2 * a := by omega
  have hlb : (l.natAbs : ℤ) = l + 2 * b := by omega
  refine ⟨k + l + b * (k + 1) + a * (l + 1) + 2 * a * b, ?_⟩
  rw [hka, hlb]
  ring

private theorem sign_sum_degree (k l : ℤ) :
    (-1 : ℂ) ^ (k.natAbs + l.natAbs + 1) =
      (-1 : ℂ) ^ (k + l - 1) := by
  have h : Even (((k.natAbs + l.natAbs + 1 : ℕ) : ℤ) - (k + l - 1)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using even_sum_degree k l
  exact sign_of_even_nat h

private theorem sign_delta_degree (k : ℤ) :
    (-1 : ℂ) ^ (k.natAbs + 1) = (-1 : ℂ) ^ (k - 1) := by
  have h : Even (((k.natAbs + 1 : ℕ) : ℤ) - (k - 1)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using even_delta_degree k
  exact sign_of_even_nat h

private theorem sign_leibniz_degree (k l : ℤ) :
    (-1 : ℂ) ^ ((k.natAbs + 1) * l.natAbs) =
      (-1 : ℂ) ^ ((k - 1) * l) := by
  have h : Even (((((k.natAbs + 1) * l.natAbs : ℕ) : ℤ)) - (k - 1) * l) := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
      even_leibniz_degree k l
  exact sign_of_even_nat h

private theorem sign_jacobi_degree (k l : ℤ) :
    (-1 : ℂ) ^ ((k.natAbs + 1) * (l.natAbs + 1)) =
      (-1 : ℂ) ^ ((k - 1) * (l - 1)) := by
  have h : Even (((((k.natAbs + 1) * (l.natAbs + 1) : ℕ) : ℤ)) -
      (k - 1) * (l - 1)) := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
      even_jacobi_degree k l
  exact sign_of_even_nat h

private theorem sign_delta_label (k : ℤ) :
    (-1 : ℂ) ^ (k.natAbs + 1) =
      (-1 : ℂ) ^ (k - 1).natAbs := by
  calc
    (-1 : ℂ) ^ (k.natAbs + 1) = (-1 : ℂ) ^ (k - 1) := sign_delta_degree k
    _ = (-1 : ℂ) ^ (k - 1).natAbs := neg_one_zpow_natAbs (k - 1)

private theorem sign_sum_label (k l : ℤ) :
    (-1 : ℂ) ^ (k.natAbs + l.natAbs + 1) =
      (-1 : ℂ) ^ (k + l - 1).natAbs := by
  calc
    (-1 : ℂ) ^ (k.natAbs + l.natAbs + 1) =
        (-1 : ℂ) ^ (k + l - 1) := sign_sum_degree k l
    _ = (-1 : ℂ) ^ (k + l - 1).natAbs :=
      neg_one_zpow_natAbs (k + l - 1)

private theorem bracket_label_eq
    (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1)
    (p q : ℕ) (u v : Cohomology D H h26 hHG hGH)
    (hs : (-1 : ℂ) ^ p = (-1 : ℂ) ^ q) :
    bracket D H h26 hHG hGH p u v = bracket D H h26 hHG hGH q u v := by
  rw [bracket_apply D H h26 hHG hGH p u v,
    bracket_apply D H h26 hHG hGH q u v, hs]

/-! The actual integer-labeled bracket is the supplied bracket with the
    justified natural sign label k.natAbs. -/

def integerBracket
    (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) (k : ℤ) :
    Cohomology D H h26 hHG hGH →ₗ[ℂ]
      Cohomology D H h26 hHG hGH →ₗ[ℂ]
        Cohomology D H h26 hHG hGH :=
  bracket D H h26 hHG hGH k.natAbs

theorem integerBracket_apply
    (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) (k : ℤ)
    (u v : Cohomology D H h26 hHG hGH) :
    integerBracket D H h26 hHG hGH k u v =
      (-1 : ℂ) ^ k • Delta D H h26 hHG hGH
          (product D H h26 hHG hGH u v) -
      (-1 : ℂ) ^ k • product D H h26 hHG hGH
          (Delta D H h26 hHG hGH u) v -
      product D H h26 hHG hGH u
          (Delta D H h26 hHG hGH v) := by
  unfold integerBracket
  rw [bracket_apply D H h26 hHG hGH k.natAbs u v]
  rw [← neg_one_zpow_natAbs k]

/-! The bracket has the requested integer degree k+l-1 on the existing grade
    submodules.  Each summand is closed using the supplied product and Delta
    degree laws; no generic closure theorem is imported. -/

theorem integerBracket_mem_grade
    (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) (k l : ℤ)
    (u v : Cohomology D H h26 hHG hGH)
    (hu : u ∈ grade D H h26 hHG hGH k)
    (hv : v ∈ grade D H h26 hHG hGH l) :
    integerBracket D H h26 hHG hGH k u v ∈
      grade D H h26 hHG hGH (k + l - 1) := by
  have hp : product D H h26 hHG hGH u v ∈
      grade D H h26 hHG hGH (k + l) :=
    product_mem_grade D H h26 hHG hGH k l u v hu hv
  have hΔp : Delta D H h26 hHG hGH
      (product D H h26 hHG hGH u v) ∈
      grade D H h26 hHG hGH (k + l - 1) :=
    Delta_lowers_ghost_number D H h26 hHG hGH (k + l) _ hp
  have hΔu : Delta D H h26 hHG hGH u ∈
      grade D H h26 hHG hGH (k - 1) :=
    Delta_lowers_ghost_number D H h26 hHG hGH k u hu
  have hΔv : Delta D H h26 hHG hGH v ∈
      grade D H h26 hHG hGH (l - 1) :=
    Delta_lowers_ghost_number D H h26 hHG hGH l v hv
  have hleft : product D H h26 hHG hGH
      (Delta D H h26 hHG hGH u) v ∈
      grade D H h26 hHG hGH (k + l - 1) := by
    simpa only [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      product_mem_grade D H h26 hHG hGH (k - 1) l
        (Delta D H h26 hHG hGH u) v hΔu hv
  have hright : product D H h26 hHG hGH u
      (Delta D H h26 hHG hGH v) ∈
      grade D H h26 hHG hGH (k + l - 1) := by
    simpa only [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      product_mem_grade D H h26 hHG hGH k (l - 1)
        u (Delta D H h26 hHG hGH v) hu hΔv
  let q : Module.End ℂ (Cohomology D H h26 hHG hGH) :=
    Pi D H h26 hHG hGH (k + l - 1)
  let x : Cohomology D H h26 hHG hGH :=
    Delta D H h26 hHG hGH (product D H h26 hHG hGH u v)
  let y : Cohomology D H h26 hHG hGH :=
    product D H h26 hHG hGH (Delta D H h26 hHG hGH u) v
  let z : Cohomology D H h26 hHG hGH :=
    product D H h26 hHG hGH u (Delta D H h26 hHG hGH v)
  have hx : x ∈ grade D H h26 hHG hGH (k + l - 1) := by
    simpa only [x] using hΔp
  have hy : y ∈ grade D H h26 hHG hGH (k + l - 1) := by
    simpa only [y] using hleft
  have hz : z ∈ grade D H h26 hHG hGH (k + l - 1) := by
    simpa only [z] using hright
  have hxfix : q x = x := by
    simpa only [q] using
      (mem_grade D H h26 hHG hGH (k + l - 1) x).mp hx
  have hyfix : q y = y := by
    simpa only [q] using
      (mem_grade D H h26 hHG hGH (k + l - 1) y).mp hy
  have hzfix : q z = z := by
    simpa only [q] using
      (mem_grade D H h26 hHG hGH (k + l - 1) z).mp hz
  apply (mem_grade D H h26 hHG hGH (k + l - 1) _).mpr
  rw [integerBracket_apply D H h26 hHG hGH k u v]
  change q (((-1 : ℂ) ^ k) • x - ((-1 : ℂ) ^ k) • y - z) =
    ((-1 : ℂ) ^ k) • x - ((-1 : ℂ) ^ k) • y - z
  simp only [map_sub, map_smul, hxfix, hyfix, hzfix]

theorem integerBracket_parity
    (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) (k l : ℤ)
    (u v : Cohomology D H h26 hHG hGH)
    (hu : u ∈ grade D H h26 hHG hGH k)
    (hv : v ∈ grade D H h26 hHG hGH l) :
    LatticeBRSTCohomologyField.parity D H h26 hHG hGH
        (integerBracket D H h26 hHG hGH k u v) =
      (-1 : ℂ) ^ (k + l - 1) •
        integerBracket D H h26 hHG hGH k u v := by
  have h := bracket_parity D H h26 hHG hGH k.natAbs l.natAbs u v
      (by simpa only [neg_one_zpow_natAbs] using
        grade_parity D H h26 hHG hGH k u hu)
      (by simpa only [neg_one_zpow_natAbs] using
        grade_parity D H h26 hHG hGH l v hv)
  change LatticeBRSTCohomologyField.parity D H h26 hHG hGH
      (bracket D H h26 hHG hGH k.natAbs u v) =
      (-1 : ℂ) ^ (k + l - 1) •
        bracket D H h26 hHG hGH k.natAbs u v
  rw [h, sign_sum_degree k l]

/-! Integer specializations of the supplied super-Leibniz, skew, Delta, and
    Jacobi endpoints.  The Jacobi statement leaves w an arbitrary full class. -/

theorem integerBracket_leibniz
    (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) (k l : ℤ)
    (u v w : Cohomology D H h26 hHG hGH)
    (hu : u ∈ grade D H h26 hHG hGH k)
    (hv : v ∈ grade D H h26 hHG hGH l) :
    integerBracket D H h26 hHG hGH k u
        (product D H h26 hHG hGH v w) =
      product D H h26 hHG hGH
          (integerBracket D H h26 hHG hGH k u v) w +
        (-1 : ℂ) ^ ((k - 1) * l) •
          product D H h26 hHG hGH v
            (integerBracket D H h26 hHG hGH k u w) := by
  have h := bracket_leibniz D H h26 hHG hGH k.natAbs l.natAbs u v w
      (by simpa only [neg_one_zpow_natAbs] using
        grade_parity D H h26 hHG hGH k u hu)
      (by simpa only [neg_one_zpow_natAbs] using
        grade_parity D H h26 hHG hGH l v hv)
  rw [sign_leibniz_degree k l] at h
  exact h

theorem integerBracket_antisymmetric
    (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) (k l : ℤ)
    (u v : Cohomology D H h26 hHG hGH)
    (hu : u ∈ grade D H h26 hHG hGH k)
    (hv : v ∈ grade D H h26 hHG hGH l) :
    integerBracket D H h26 hHG hGH k u v =
      -((-1 : ℂ) ^ ((k - 1) * (l - 1))) •
        integerBracket D H h26 hHG hGH l v u := by
  have h := bracket_antisymmetric D H h26 hHG hGH k.natAbs l.natAbs u v
      (by simpa only [neg_one_zpow_natAbs] using
        grade_parity D H h26 hHG hGH k u hu)
      (by simpa only [neg_one_zpow_natAbs] using
        grade_parity D H h26 hHG hGH l v hv)
  rw [sign_jacobi_degree k l] at h
  exact h

theorem integerBracket_delta_compatible
    (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) (k : ℤ)
    (u v : Cohomology D H h26 hHG hGH) :
    Delta D H h26 hHG hGH
        (integerBracket D H h26 hHG hGH k u v) =
      integerBracket D H h26 hHG hGH (k - 1)
          (Delta D H h26 hHG hGH u) v +
        (-1 : ℂ) ^ (k - 1) •
          integerBracket D H h26 hHG hGH k u
            (Delta D H h26 hHG hGH v) := by
  have h := bracket_delta D H h26 hHG hGH k.natAbs u v
  have hlabel := bracket_label_eq D H h26 hHG hGH
    (k.natAbs + 1) (k - 1).natAbs
    (Delta D H h26 hHG hGH u) v (sign_delta_label k)
  rw [hlabel, sign_delta_degree k] at h
  exact h

theorem integerBracket_jacobi
    (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) (k l : ℤ)
    (u v w : Cohomology D H h26 hHG hGH)
    (hu : u ∈ grade D H h26 hHG hGH k)
    (hv : v ∈ grade D H h26 hHG hGH l) :
    integerBracket D H h26 hHG hGH k u
        (integerBracket D H h26 hHG hGH l v w) =
      integerBracket D H h26 hHG hGH (k + l - 1)
          (integerBracket D H h26 hHG hGH k u v) w +
        (-1 : ℂ) ^ ((k - 1) * (l - 1)) •
          integerBracket D H h26 hHG hGH l v
            (integerBracket D H h26 hHG hGH k u w) := by
  have h := bracket_jacobi D H h26 hHG hGH k.natAbs l.natAbs u v w
      (by simpa only [neg_one_zpow_natAbs] using
        grade_parity D H h26 hHG hGH k u hu)
      (by simpa only [neg_one_zpow_natAbs] using
        grade_parity D H h26 hHG hGH l v hv)
  have hlabel := bracket_label_eq D H h26 hHG hGH
      (k.natAbs + l.natAbs + 1) (k + l - 1).natAbs
      (bracket D H h26 hHG hGH k.natAbs u v) w (sign_sum_label k l)
  rw [hlabel, sign_jacobi_degree k l] at h
  exact h

end
end D5.S3.VertexAlgebra.LatticeBRSTGhostNumberBracket
