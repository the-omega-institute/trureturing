import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.TernaryComparisonProduct
import D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
import Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
import Reg.Support.DependentFamily
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.Perm.Basic

/-! Source-bound audits of products of ternary comparison structures.

The rejected laws use four transformations of comparison structures: transport along an
equivalence of carriers, the discrete reading that keeps the transfer and reads one exactly on
the diagonal and zero elsewhere, the group structure of a group with the discrete reading, and
the half-shifted reading `(1 + kappa) / 2`. The models are the two-point structure, the unit
quaternion model lifted to an arbitrary universe, and the symmetric group on three letters
together with a commutative structure on the same carrier. -/

namespace Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonProduct

open _root_.D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
open _root_.D5.S3.Quantum.AURICOmega.TernaryComparisonProduct
open _root_.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
  (twoPoint featureTrue featureFalse twoPoint_commutes)
open scoped InnerProductSpace Quaternion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section
universe u v w

/-! Transformations of comparison structures. -/

open Classical in
/-- The Gram form of the discrete reading is a sum of squares over the values of the family. -/
theorem discrete_gram_nonneg {X : Type w} (n : ℕ) (x : Fin n → X) (c : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * (if x i = x j then (1 : ℝ) else 0) := by
  let A : Fin n → X → ℝ := fun i a => if x i = a then 1 else 0
  have key : ∀ i j, (if x i = x j then (1 : ℝ) else 0) =
      ∑ a ∈ Finset.univ.image x, A i a * A j a := by
    intro i j
    simp only [A, boole_mul]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_image_of_mem x (Finset.mem_univ i), ↓reduceIte]
    by_cases h : x i = x j
    · simp [h]
    · simp [h, Ne.symm h]
  have expand : ∑ a ∈ Finset.univ.image x, (∑ i, c i * A i a) * (∑ j, c j * A j a) =
      ∑ i, ∑ j, c i * c j * (if x i = x j then (1 : ℝ) else 0) := by
    simp_rw [Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [key, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [← expand]
  exact Finset.sum_nonneg fun a _ => mul_self_nonneg _

/-- The transfer cancels its first argument against equal outer arguments. -/
theorem tri_right_inj {M : Type w} (C : TernaryComparison M) (x y u v : M) :
    C.tri x u v = C.tri y u v ↔ x = y := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have h' := congrArg (fun z => C.tri z v u) h
  simpa only [C.tri_assoc, C.tri_self_left, C.tri_self_right] using h'

/-- The transfer cancels its last argument against equal inner arguments. -/
theorem tri_left_inj {M : Type w} (C : TernaryComparison M) (u v x y : M) :
    C.tri u v x = C.tri u v y ↔ x = y := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have h' := congrArg (fun z => C.tri v u z) h
  simpa only [← C.tri_assoc, C.tri_self_left, C.tri_self_right] using h'

open Classical in
/-- The same transfer with the discrete reading. -/
def discrete {M : Type w} (C : TernaryComparison M) : TernaryComparison M where
  tri := C.tri
  kappa x y := if x = y then 1 else 0
  tri_self_left := C.tri_self_left
  tri_self_right := C.tri_self_right
  tri_assoc := C.tri_assoc
  kappa_symm x y := by
    by_cases h : x = y
    · simp [h]
    · simp [h, Ne.symm h]
  kappa_eq_one_iff x y := by by_cases h : x = y <;> simp [h]
  kappa_nonneg x y := by split_ifs <;> norm_num
  kappa_tri_right x y u v := by simp only [tri_right_inj]
  kappa_tri_left u v x y := by simp only [tri_left_inj]
  kappa_gram_nonneg n x c := discrete_gram_nonneg n x c

open Classical in
/-- The group transfer `x * y⁻¹ * z` with the discrete reading. -/
def groupHeap (G : Type w) [Group G] : TernaryComparison G where
  tri x y z := x * y⁻¹ * z
  kappa x y := if x = y then 1 else 0
  tri_self_left x z := by rw [mul_inv_cancel, one_mul]
  tri_self_right x z := inv_mul_cancel_right x z
  tri_assoc x y z u v := by simp only [mul_assoc]
  kappa_symm x y := by
    by_cases h : x = y
    · simp [h]
    · simp [h, Ne.symm h]
  kappa_eq_one_iff x y := by by_cases h : x = y <;> simp [h]
  kappa_nonneg x y := by split_ifs <;> norm_num
  kappa_tri_right x y u v := by simp only [mul_left_inj]
  kappa_tri_left u v x y := by simp only [mul_assoc, mul_right_inj]
  kappa_gram_nonneg n x c := discrete_gram_nonneg n x c

/-- Transport of a comparison structure along an equivalence of carriers. -/
def transport {X : Type u} {Y : Type w} (e : X ≃ Y) (C : TernaryComparison Y) :
    TernaryComparison X where
  tri x y z := e.symm (C.tri (e x) (e y) (e z))
  kappa x y := C.kappa (e x) (e y)
  tri_self_left x z := by simp only [C.tri_self_left, Equiv.symm_apply_apply]
  tri_self_right x z := by simp only [C.tri_self_right, Equiv.symm_apply_apply]
  tri_assoc x y z u v := by simp only [Equiv.apply_symm_apply, C.tri_assoc]
  kappa_symm x y := C.kappa_symm _ _
  kappa_eq_one_iff x y := by rw [C.kappa_eq_one_iff, e.apply_eq_iff_eq]
  kappa_nonneg x y := C.kappa_nonneg _ _
  kappa_tri_right x y u v := by
    simp only [Equiv.apply_symm_apply]
    exact C.kappa_tri_right _ _ _ _
  kappa_tri_left u v x y := by
    simp only [Equiv.apply_symm_apply]
    exact C.kappa_tri_left _ _ _ _
  kappa_gram_nonneg n x c := C.kappa_gram_nonneg n (fun i => e (x i)) c

/-- The half-shifted reading `(1 + kappa) / 2` with the same transfer. -/
def halfShift {M : Type w} (C : TernaryComparison M) : TernaryComparison M where
  tri := C.tri
  kappa x y := (1 + C.kappa x y) / 2
  tri_self_left := C.tri_self_left
  tri_self_right := C.tri_self_right
  tri_assoc := C.tri_assoc
  kappa_symm x y := by rw [C.kappa_symm]
  kappa_eq_one_iff x y := by
    rw [← C.kappa_eq_one_iff]
    constructor <;> intro h <;> linarith
  kappa_nonneg x y := by
    have := C.kappa_nonneg x y
    positivity
  kappa_tri_right x y u v := by rw [C.kappa_tri_right]
  kappa_tri_left u v x y := by rw [C.kappa_tri_left]
  kappa_gram_nonneg n x c := by
    have h1 := C.kappa_gram_nonneg n x c
    have key : ∑ i, ∑ j, c i * c j * ((1 + C.kappa (x i) (x j)) / 2) =
        (1 / 2) * ((∑ i, c i) * (∑ j, c j)) +
          (1 / 2) * ∑ i, ∑ j, c i * c j * C.kappa (x i) (x j) := by
      rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [key]
    have h2 := mul_self_nonneg (∑ i, c i)
    linarith

theorem prod_kappa_apply {M : Type u} {N : Type v} (C : TernaryComparison M)
    (D : TernaryComparison N) (p q : M × N) :
    (prod C D).kappa p q = C.kappa p.1 q.1 * D.kappa p.2 q.2 := rfl

theorem discrete_kappa_of_ne {M : Type w} (C : TernaryComparison M) {x y : M} (h : x ≠ y) :
    (discrete C).kappa x y = 0 := by
  classical
  change (if x = y then (1 : ℝ) else 0) = 0
  simp [h]

theorem halfShift_kappa_ge {M : Type w} (C : TernaryComparison M) (x y : M) :
    1 / 2 ≤ (halfShift C).kappa x y := by
  have := C.kappa_nonneg x y
  change 1 / 2 ≤ (1 + C.kappa x y) / 2
  linarith

/-- A structure on a nonempty carrier is not the Gram kernel of a map into zero-space. -/
theorem not_hasFeatureRank_zero {M : Type w} (C : TernaryComparison M) (x : M) :
    ¬ C.HasFeatureRank 0 := by
  rintro ⟨φ, hφ⟩
  have h := hφ x x
  rw [C.kappa_self, Subsingleton.elim (φ x) 0, inner_zero_left] at h
  exact one_ne_zero h

theorem transport_hasFeatureRank {X : Type u} {Y : Type w} (e : X ≃ Y) (C : TernaryComparison Y)
    {r : ℕ} (h : C.HasFeatureRank r) : (transport e C).HasFeatureRank r := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨fun x => φ (e x), fun x y => hφ (e x) (e y)⟩

theorem transport_chainConnected {X : Type u} {Y : Type w} (e : X ≃ Y)
    (C : TernaryComparison Y) (h : C.ChainConnected) : (transport e C).ChainConnected := by
  intro ε hε x y
  have hc := Relation.ReflTransGen.lift (p := fun a b : X => 1 - ε < (transport e C).kappa a b)
    e.symm (fun a b hab => by
      change 1 - ε < C.kappa (e (e.symm a)) (e (e.symm b))
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact hab) _ _ (h ε hε (e x) (e y))
  simpa only [Function.onFun, Equiv.symm_apply_apply] using hc

/-! Models. -/

/-- The unit quaternion model on a lifted carrier. -/
def liftQ : TernaryComparison (ULift.{u} (unitary ℍ[ℝ])) :=
  transport Equiv.ulift quaternionModel

theorem liftQ_chainConnected : liftQ.{u}.ChainConnected :=
  transport_chainConnected _ _ quaternionModel_chainConnected

theorem liftQ_hasFeatureRank_five : liftQ.{u}.HasFeatureRank 5 :=
  transport_hasFeatureRank _ _ quaternionModel_hasFeatureRank_five

theorem unit_neg_one_ne_one : (⟨-1⟩ : ULift.{u} (unitary ℍ[ℝ])) ≠ ⟨1⟩ := by
  intro h
  have h' := congrArg (fun z : ULift.{u} (unitary ℍ[ℝ]) => ((z.down : ℍ[ℝ])).re) h
  simp only [Unitary.coe_neg, OneMemClass.coe_one, Quaternion.re_neg, Quaternion.re_one] at h'
  norm_num at h'

/-- The symmetric group on three letters with the discrete reading, on a lifted carrier. -/
def symThree : TernaryComparison (ULift.{u} (Equiv.Perm (Fin 3))) :=
  transport Equiv.ulift (groupHeap (Equiv.Perm (Fin 3)))

theorem symThree_noncommutative : symThree.{u}.Noncommutative := by
  refine ⟨⟨Equiv.swap 0 1⟩, ⟨1⟩, ⟨Equiv.swap 1 2⟩, ?_⟩
  change ULift.up (Equiv.swap (0 : Fin 3) 1 * 1⁻¹ * Equiv.swap 1 2) ≠
    ULift.up (Equiv.swap (1 : Fin 3) 2 * 1⁻¹ * Equiv.swap 0 1)
  decide

theorem card_symThree_carrier :
    Fintype.card (ULift.{u} (Equiv.Perm (Fin 3))) = Fintype.card (Multiplicative (ZMod 6)) := by
  rfl

/-- In a commutative group the transfer `a * b⁻¹ * c` is symmetric in `a` and `c`. -/
theorem heap_comm {G : Type w} [CommGroup G] (a b c : G) : a * b⁻¹ * c = c * b⁻¹ * a := by
  rw [mul_right_comm, mul_comm a c, mul_right_comm]

/-- A commutative structure on the carrier of `symThree`: the cyclic group of order six with the
discrete reading, transported along a bijection. -/
def cyclicSix : TernaryComparison (ULift.{u} (Equiv.Perm (Fin 3))) :=
  transport (Fintype.equivOfCardEq card_symThree_carrier) (groupHeap (Multiplicative (ZMod 6)))

theorem cyclicSix_commutes : ¬ cyclicSix.{u}.Noncommutative := by
  rintro ⟨x, y, z, h⟩
  apply h
  change (Fintype.equivOfCardEq card_symThree_carrier).symm (_ * _⁻¹ * _) =
    (Fintype.equivOfCardEq card_symThree_carrier).symm (_ * _⁻¹ * _)
  congr 1
  exact heap_comm _ _ _

/-- A structure without order-sensitive triples has all triples order-insensitive. -/
theorem tri_comm_of_not {M : Type w} (C : TernaryComparison M) (h : ¬ C.Noncommutative)
    (x y z : M) : C.tri x y z = C.tri z y x := by
  by_contra hne
  exact h ⟨x, y, z, hne⟩

theorem twoPoint_touchesZero : twoPoint.{u}.TouchesZero := by
  intro ε hε
  refine ⟨⟨true⟩, ⟨false⟩, ?_⟩
  change featureTrue (⟨true⟩ : ULift.{u} Bool) * featureTrue (⟨false⟩ : ULift.{u} Bool) +
    featureFalse (⟨true⟩ : ULift.{u} Bool) * featureFalse (⟨false⟩ : ULift.{u} Bool) < ε
  norm_num [featureTrue, featureFalse]
  exact hε

theorem twoPoint_ne_halfShift : twoPoint.{u} ≠ halfShift twoPoint.{u} := by
  intro h
  have h' := congrArg (fun t : TernaryComparison (ULift.{u} Bool) => t.kappa ⟨true⟩ ⟨false⟩) h
  change featureTrue (⟨true⟩ : ULift.{u} Bool) * featureTrue (⟨false⟩ : ULift.{u} Bool) +
      featureFalse (⟨true⟩ : ULift.{u} Bool) * featureFalse (⟨false⟩ : ULift.{u} Bool) =
    (1 + (featureTrue (⟨true⟩ : ULift.{u} Bool) * featureTrue (⟨false⟩ : ULift.{u} Bool) +
      featureFalse (⟨true⟩ : ULift.{u} Bool) * featureFalse (⟨false⟩ : ULift.{u} Bool))) / 2 at h'
  norm_num [featureTrue, featureFalse] at h'

/-! The rank of the product feature map, for `prod_hasFeatureRank`. -/
namespace Rank

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p s => p * s) (fun e => nomatch e)

def constant : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the complete carrier, structure, rank and hypothesis telescope of
`prod_hasFeatureRank`. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {M : Type u} {N : Type v} (C : TernaryComparison M) (D : TernaryComparison N)
    {k l : ℕ}, C.HasFeatureRank k → D.HasFeatureRank l →
      (prod C D).HasFeatureRank (r.readout () k l)

theorem rejected_law : ¬ arena.{u, v}.Law constant := by
  intro h
  have hh := h liftQ.{u} liftQ.{v} liftQ_hasFeatureRank_five liftQ_hasFeatureRank_five
  exact not_hasFeatureRank_zero _ (⟨1⟩, ⟨1⟩) hh

theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  exact ⟨1, 0, 1, by decide⟩

def source_registration :
    Registration arena.{u, v} (type_of% @prod_hasFeatureRank.{u, v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@prod_hasFeatureRank.{u, v}, constant, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨constant, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Rank

/-! The left factor inside the product, for the three transfer statements. -/
namespace Factor

abbrev signature : Signature where
  Params := Type u
  State p := TernaryComparison p
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := TernaryComparison p
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ s => s) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  exact ⟨ULift.{u} Bool, twoPoint, halfShift twoPoint, twoPoint_ne_halfShift⟩

/-- The discrete reading on the left factor. -/
def discreteLeft : Realization signature.{u} :=
  realize signature (fun _ _ s => discrete s) (fun e => nomatch e)

/-- The half-shifted reading on the left factor. -/
def halfLeft : Realization signature.{u} :=
  realize signature (fun _ _ s => halfShift s) (fun e => nomatch e)

open Classical in
/-- A commutative structure on the left carrier whenever one exists. -/
def commutativeLeft : Realization signature.{u} :=
  realize signature
    (fun _ p s => if h : ∃ t : TernaryComparison p, ¬ t.Noncommutative then h.choose else s)
    (fun e => nomatch e)

/-- Retain the complete carrier, structure and hypothesis telescope of `prod_chainConnected`. -/
abbrev chainArena : Arena where
  signature := signature.{u}
  Law r := ∀ {M : Type u} {N : Type v} (C : TernaryComparison M) (D : TernaryComparison N),
    C.ChainConnected → D.ChainConnected → (prod (r.readout () M C) D).ChainConnected

open Classical in
theorem chain_rejected : ¬ chainArena.{u, v}.Law discreteLeft := by
  intro h
  have hh := h liftQ.{u} liftQ.{v} liftQ_chainConnected liftQ_chainConnected (1 / 2)
    (by norm_num) (⟨-1⟩, ⟨1⟩) (⟨1⟩, ⟨1⟩)
  have key : ∀ b c : ULift.{u} (unitary ℍ[ℝ]) × ULift.{v} (unitary ℍ[ℝ]),
      1 - 1 / 2 < (prod (discrete liftQ.{u}) liftQ.{v}).kappa b c → b.1 = c.1 := by
    intro b c hbc
    by_contra hne
    rw [prod_kappa_apply, discrete_kappa_of_ne _ hne, zero_mul] at hbc
    norm_num at hbc
  have hfst : ∀ c, Relation.ReflTransGen
      (fun a b => 1 - 1 / 2 < (prod (discrete liftQ.{u}) liftQ.{v}).kappa a b)
      ((⟨-1⟩, ⟨1⟩) : ULift.{u} (unitary ℍ[ℝ]) × ULift.{v} (unitary ℍ[ℝ])) c →
      c.1 = ⟨-1⟩ := by
    intro c hc
    induction hc with
    | refl => rfl
    | tail _ hbc ih => exact (key _ _ hbc).symm.trans ih
  exact unit_neg_one_ne_one.{u} (hfst _ hh).symm

def chain_registration :
    Registration chainArena.{u, v} (type_of% @prod_chainConnected.{u, v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@prod_chainConnected.{u, v}, discreteLeft, chain_rejected⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨discreteLeft, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, chain_rejected⟩
    · intro e
      exact nomatch e
  dependence := dependence

/-- Retain the complete carrier, structure, instance and hypothesis telescope of
`prod_noncommutative_left`. -/
abbrev orderArena : Arena where
  signature := signature.{u}
  Law r := ∀ {M : Type u} {N : Type v} (C : TernaryComparison M) (D : TernaryComparison N)
    [Nonempty N], C.Noncommutative → (prod (r.readout () M C) D).Noncommutative

open Classical in
theorem order_rejected : ¬ orderArena.{u, v}.Law commutativeLeft := by
  intro h
  have hex : ∃ t : TernaryComparison (ULift.{u} (Equiv.Perm (Fin 3))), ¬ t.Noncommutative :=
    ⟨cyclicSix, cyclicSix_commutes⟩
  have hh := h symThree.{u} twoPoint.{v} symThree_noncommutative
  change (prod (if h : ∃ t : TernaryComparison (ULift.{u} (Equiv.Perm (Fin 3))),
    ¬ t.Noncommutative then h.choose else symThree) twoPoint).Noncommutative at hh
  simp only [hex, ↓reduceDIte] at hh
  obtain ⟨x, y, z, hne⟩ := hh
  exact hne (Prod.ext (tri_comm_of_not _ hex.choose_spec x.1 y.1 z.1)
    (tri_comm_of_not _ twoPoint_commutes x.2 y.2 z.2))

def order_registration :
    Registration orderArena.{u, v} (type_of% @prod_noncommutative_left.{u, v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@prod_noncommutative_left.{u, v}, commutativeLeft, order_rejected⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨commutativeLeft, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, order_rejected⟩
    · intro e
      exact nomatch e
  dependence := dependence

/-- Retain the complete carrier, structure, instance and hypothesis telescope of
`prod_touchesZero_left`. -/
abbrev zeroArena : Arena where
  signature := signature.{u}
  Law r := ∀ {M : Type u} {N : Type v} (C : TernaryComparison M) (D : TernaryComparison N)
    [Nonempty N], C.TouchesZero → (prod (r.readout () M C) D).TouchesZero

theorem zero_rejected : ¬ zeroArena.{u, v}.Law halfLeft := by
  intro h
  obtain ⟨x, y, hxy⟩ :=
    h twoPoint.{u} (halfShift twoPoint.{v}) twoPoint_touchesZero (1 / 8) (by norm_num)
  change (halfShift twoPoint).kappa x.1 y.1 * (halfShift twoPoint).kappa x.2 y.2 < 1 / 8 at hxy
  have h1 := halfShift_kappa_ge twoPoint.{u} x.1 y.1
  have h2 := halfShift_kappa_ge twoPoint.{v} x.2 y.2
  nlinarith

def zero_registration :
    Registration zeroArena.{u, v} (type_of% @prod_touchesZero_left.{u, v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@prod_touchesZero_left.{u, v}, halfLeft, zero_rejected⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨halfLeft, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, zero_rejected⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Factor

def prod_hasFeatureRank_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@prod_hasFeatureRank.{u, v}) (Realization Rank.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonProduct.prod_hasFeatureRank_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonProduct.Rank.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Rank.arena.{u, v}⟩
  objectArena := .source ⟨Rank.arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Rank.arena.{u, v} ⟨Rank.source_registration.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Rank.signature (fun _ p s => p * s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.TernaryComparisonProduct
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def prod_chainConnected_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@prod_chainConnected.{u, v}) (Realization Factor.signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonProduct.prod_chainConnected_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonProduct.Factor.chain_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Factor.chainArena.{u, v}⟩
  objectArena := .source ⟨Factor.chainArena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Factor.chainArena.{u, v} ⟨Factor.chain_registration.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Factor.signature.{u} (fun _ _ s => s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.TernaryComparisonProduct
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def prod_noncommutative_left_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@prod_noncommutative_left.{u, v}) (Realization Factor.signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonProduct.prod_noncommutative_left_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonProduct.Factor.order_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Factor.orderArena.{u, v}⟩
  objectArena := .source ⟨Factor.orderArena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Factor.orderArena.{u, v} ⟨Factor.order_registration.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Factor.signature.{u} (fun _ _ s => s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.TernaryComparisonProduct
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def prod_touchesZero_left_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@prod_touchesZero_left.{u, v}) (Realization Factor.signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonProduct.prod_touchesZero_left_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonProduct.Factor.zero_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Factor.zeroArena.{u, v}⟩
  objectArena := .source ⟨Factor.zeroArena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Factor.zeroArena.{u, v} ⟨Factor.zero_registration.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Factor.signature.{u} (fun _ _ s => s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.TernaryComparisonProduct
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonProduct
