/- GID: D5/S3/Arith/LocalDold/QuotientBlock
   generality: G
   mirror-B: D5/B/S3/Arith/LocalDold/QuotientBlock
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual normalized blocks and nonconstant quotient coefficients have equal ideals. -/
import D5.S3.Arith.LocalDold.NormalizedQuotient
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.OrderOfElement

/-! The monic quotient pairing is unitriangular after reversing the nonconstant
coordinates. This is the actual quotient/block bridge in manuscript Section 3.1. -/
set_option autoImplicit false
namespace D5.S3.Arith.LocalDold.QuotientBlock
open Polynomial Matrix
open D5.S3.Arith.LocalDold.NormalizedQuotient

private theorem initial (E : LinearRecurrence ℤ) (i : ℕ) (hi : i < E.order) :
    impulse E i = if i+1=E.order then 1 else 0 :=
  E.mkSol_eq_init _ ⟨i,hi⟩

private theorem degree (E : LinearRecurrence ℤ) : E.charPoly.natDegree = E.order :=
  Polynomial.natDegree_eq_of_degree_eq_some E.charPoly_degree_eq_order

private noncomputable def pairing (E : LinearRecurrence ℤ) :
    Matrix (Fin (E.order-1)) (Fin (E.order-1)) ℤ :=
  fun j i => impulse E (E.order-1-i.val+j.val)

private theorem pairing_det (E : LinearRecurrence ℤ) (hk : 2 ≤ E.order) :
    (pairing E).det = 1 := by
  have hl : (pairing E).IsLowerTriangular := by
    intro j i hij
    change i.val > j.val at hij
    change impulse E (E.order-1-i.val+j.val)=0
    rw [initial E _ (by omega),ite_eq_right (by omega)]
  rw [Matrix.det_of_isLowerTriangular _ hl]
  have hd : ∀ i : Fin (E.order-1), pairing E i i=1 := by
    intro i
    change impulse E (E.order-1-i.val+i.val)=1
    rw [initial E _ (by omega),ite_eq_left (by omega)]
  simp only [hd,Finset.prod_const_one]

private theorem span_mulVec_le {I : Type*} [Fintype I] (A : Matrix I I ℤ) (v : I → ℤ) :
    Ideal.span (Set.range (A *ᵥ v)) ≤ Ideal.span (Set.range v) := by
  apply Ideal.span_le.mpr
  rintro x ⟨i,rfl⟩
  change (∑ j, A i j*v j) ∈ Ideal.span (Set.range v)
  apply Ideal.sum_mem
  intro j _
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j,rfl⟩)

private theorem span_mulVec_eq {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (hA : IsUnit A.det) (v : I → ℤ) :
    Ideal.span (Set.range (A *ᵥ v)) = Ideal.span (Set.range v) := by
  apply le_antisymm (span_mulVec_le A v)
  have he : A⁻¹ *ᵥ (A *ᵥ v)=v := by
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ hA,Matrix.one_mulVec]
  conv_lhs => rw [← he]
  exact span_mulVec_le A⁻¹ (A *ᵥ v)

private theorem quotient_expansion (E : LinearRecurrence ℤ) (hk : 2 ≤ E.order)
    (q : Algebra E) :
    (∑ i : Fin (E.order-1),
      (AdjoinRoot.modByMonicHom E.charPoly_monic q).coeff (E.order-1-i.val) •
        (AdjoinRoot.root E.charPoly)^(E.order-1-i.val)) +
      (AdjoinRoot.modByMonicHom E.charPoly_monic q).coeff 0 • (1 : Algebra E) = q := by
  have hs := (AdjoinRoot.powerBasis' E.charPoly_monic).basis.sum_repr q
  simp_rw [(AdjoinRoot.powerBasis' E.charPoly_monic).basis_eq_pow] at hs
  change (∑ i : Fin E.charPoly.natDegree,
    (AdjoinRoot.modByMonicHom E.charPoly_monic q).coeff i.val •
      (AdjoinRoot.root E.charPoly)^i.val) = q at hs
  rw [degree E] at hs
  rw [← Equiv.sum_comp (Fin.revPerm : Fin E.order ≃ Fin E.order)] at hs
  have ho : E.order=E.order-1+1 := by omega
  conv at hs => lhs; rw [ho]
  rw [Fin.sum_univ_castSucc] at hs
  simpa only [Fin.revPerm_apply,Fin.val_rev,Fin.val_castSucc,Fin.val_last,
    Nat.sub_self,pow_zero,Nat.add_sub_add_right] using hs

/-- For every actual quotient element, top-coefficient observations against the
first order-minus-one powers generate exactly its nonconstant coefficient ideal. -/
theorem observation_ideal (E : LinearRecurrence ℤ) (hk : 2 ≤ E.order) (q : Algebra E) :
    Ideal.span (Set.range (fun j : Fin (E.order-1) =>
      observation E (q*(AdjoinRoot.root E.charPoly)^j.val))) =
    Ideal.span (Set.range (fun i : Fin (E.order-1) =>
      (AdjoinRoot.modByMonicHom E.charPoly_monic q).coeff (E.order-1-i.val))) := by
  let v : Fin (E.order-1) → ℤ := fun i =>
    (AdjoinRoot.modByMonicHom E.charPoly_monic q).coeff (E.order-1-i.val)
  have he : (fun j : Fin (E.order-1) =>
      observation E (q*(AdjoinRoot.root E.charPoly)^j.val)) = pairing E *ᵥ v := by
    funext j
    conv_lhs => rw [← quotient_expansion E hk q]
    rw [add_mul,map_add,Finset.sum_mul,map_sum]
    have hz : observation E ((AdjoinRoot.modByMonicHom E.charPoly_monic q).coeff 0 •
        (1 : Algebra E) * (AdjoinRoot.root E.charPoly)^j.val)=0 := by
      rw [smul_mul_assoc,map_smul,one_mul,
        observation_eq_impulse E (by omega),initial E _ (by omega),ite_eq_right (by omega)]
      simp
    rw [hz,add_zero]
    change _ = ∑ i, pairing E j i*v i
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_mul_assoc,map_smul,← pow_add,observation_eq_impulse E (by omega)]
    change v i*impulse E (E.order-1-i.val+j.val) =
      impulse E (E.order-1-i.val+j.val)*v i
    exact mul_comm _ _
  rw [he]
  exact span_mulVec_eq (pairing E) (by rw [pairing_det E hk]; exact isUnit_one) v

/-- Apply the unitriangular pairing to the actual nth root power and impulse block.
There is no supplied block-equivalence assumption and no irreducibility hypothesis. -/
theorem block_coefficient_ideal (E : LinearRecurrence ℤ) (hk : 2 ≤ E.order) (n : ℕ) :
    Ideal.span (Set.range (fun j : Fin (E.order-1) => impulse E (n+j.val))) =
    Ideal.span (Set.range (fun i : Fin (E.order-1) =>
      (AdjoinRoot.modByMonicHom E.charPoly_monic ((AdjoinRoot.root E.charPoly)^n)).coeff
        (E.order-1-i.val))) := by
  have h := observation_ideal E hk ((AdjoinRoot.root E.charPoly)^n)
  simpa only [← pow_add,observation_eq_impulse E (by omega)] using h

#print axioms observation_ideal
#print axioms block_coefficient_ideal
private theorem scalar_iff {F : Type*} [Field F] (f : F[X]) (hf : f.Monic)
    (hk : 2 ≤ f.natDegree) (q : AdjoinRoot f) :
    (∃ a : F, q=AdjoinRoot.of f a) ↔
      ∀ i : Fin (f.natDegree-1),
        (AdjoinRoot.modByMonicHom hf q).coeff (f.natDegree-1-i.val)=0 := by
  have hfdeg : 0 < f.degree := by rw [degree_eq_natDegree hf.ne_zero]; exact_mod_cast (by omega : 0 < f.natDegree)
  constructor
  · rintro ⟨a,rfl⟩ i
    have hCa : (C a : F[X]) %ₘ f = C a :=
      (modByMonic_eq_self_iff hf).mpr ((degree_C_le).trans_lt hfdeg)
    rw [← AdjoinRoot.mk_C,AdjoinRoot.modByMonicHom_mk,hCa,coeff_C,ite_eq_right (by omega)]
  · intro hc
    let P := AdjoinRoot.modByMonicHom hf q
    have hPdeg : P.degree < f.degree := by
      obtain ⟨p,rfl⟩ := AdjoinRoot.mk_surjective q
      exact degree_modByMonic_lt p hf
    have he : P=C (P.coeff 0) := by
      ext m
      by_cases hm0 : m=0
      · simp [hm0]
      · rw [coeff_C,ite_eq_right (by omega)]
        by_cases hm : m < f.natDegree
        · let i : Fin (f.natDegree-1) := ⟨f.natDegree-1-m,by omega⟩
          have hi : f.natDegree-1-i.val=m := by dsimp [i];omega
          simpa only [hi] using hc i
        · apply coeff_eq_zero_of_degree_lt
          apply lt_of_lt_of_le hPdeg
          rw [degree_eq_natDegree hf.ne_zero]
          exact_mod_cast (by omega : f.natDegree ≤ m)
    refine ⟨P.coeff 0,?_⟩
    calc
      q = AdjoinRoot.mk f P := (AdjoinRoot.mk_leftInverse hf q).symm
      _ = AdjoinRoot.of f (P.coeff 0) := by
        conv_lhs => rw [he]
        rw [AdjoinRoot.mk_C]

private theorem finite_scalar_rank {F : Type*} [Field F] [Finite F]
    (f : F[X]) (hf : f.Monic) (hk : 2 ≤ f.natDegree) (h0 : f.coeff 0 ≠ 0) :
    ∃ r : ℕ, 0 < r ∧ ∀ n : ℕ,
      (∀ i : Fin (f.natDegree-1),
        (AdjoinRoot.modByMonicHom hf ((AdjoinRoot.root f)^n)).coeff
          (f.natDegree-1-i.val)=0) ↔ r ∣ n := by
  let A := AdjoinRoot f
  letI : Finite A := Finite.of_equiv (Fin f.natDegree → F)
    (AdjoinRoot.powerBasisAux' hf).equivFun.toEquiv.symm
  letI : Nontrivial A := (AdjoinRoot.nontrivial_iff_of_monic hf).mpr (by
    rw [degree_eq_natDegree hf.ne_zero];exact_mod_cast (by omega : 0 < f.natDegree))
  have hu : IsUnit (AdjoinRoot.root f) := by
    have he := congrArg (AdjoinRoot.mk f) (X_mul_divX_add f)
    simp only [map_add,map_mul,AdjoinRoot.mk_X,AdjoinRoot.mk_C,AdjoinRoot.mk_self] at he
    have hc : IsUnit (AdjoinRoot.of f (f.coeff 0)) :=
      (isUnit_iff_ne_zero.mpr h0).map (AdjoinRoot.of f)
    have hm : AdjoinRoot.root f * AdjoinRoot.mk f f.divX = -AdjoinRoot.of f (f.coeff 0) :=
      eq_neg_of_add_eq_zero_left he
    exact isUnit_of_mul_isUnit_left (hm.symm ▸ hc.neg)
  let x : Aˣ := hu.unit
  have hx : (x : A)=AdjoinRoot.root f := hu.unit_spec
  let H : Subgroup Aˣ := (Units.map (AdjoinRoot.of f).toMonoidHom).range
  let y : Aˣ ⧸ H := QuotientGroup.mk x
  refine ⟨orderOf y,orderOf_pos y,?_⟩
  intro n
  rw [← scalar_iff f hf hk]
  have hs : (∃ a : F, (AdjoinRoot.root f)^n=AdjoinRoot.of f a) ↔
      x^n ∈ H := by
    constructor
    · rintro ⟨a,ha⟩
      have hane : a ≠ 0 := by
        intro hz
        have hun := hu.pow n
        rw [ha,hz,map_zero] at hun
        exact not_isUnit_zero hun
      refine ⟨Units.mk0 a hane,?_⟩
      apply Units.ext
      change AdjoinRoot.of f a = (x : A)^n
      rw [hx]
      exact ha.symm
    · rintro ⟨a,ha⟩
      refine ⟨a.val,?_⟩
      have he := congrArg Units.val ha
      change AdjoinRoot.of f a.val = (x : A)^n at he
      rw [hx] at he
      exact he.symm
  rw [hs,orderOf_dvd_iff_pow_eq_one]
  change x^n ∈ H ↔ (QuotientGroup.mk x : Aˣ ⧸ H)^n=1
  rw [← QuotientGroup.mk_pow,QuotientGroup.eq_one_iff]

private theorem powers_remainder {R : Type*} [CommRing R] (f : R[X]) (hf : f.Monic) (n : ℕ) :
    AdjoinRoot.modByMonicHom hf ((AdjoinRoot.root f)^n) = (X^n : R[X]) %ₘ f := by
  rw [← AdjoinRoot.mk_X,← map_pow,AdjoinRoot.modByMonicHom_mk]

private theorem span_divisibility {I : Type*} (v : I → ℤ) (d : ℤ) :
    (∀ i, d ∣ v i) ↔ Ideal.span (Set.range v) ≤ Ideal.span {d} := by
  rw [Ideal.span_le]
  constructor
  · intro h x hx
    obtain ⟨i,rfl⟩ := hx
    exact Ideal.mem_span_singleton.mpr (h i)
  · intro h i
    exact Ideal.mem_span_singleton.mp (h ⟨i,rfl⟩)

/-- At every prime where the actual quotient root is a unit, divisibility of the
whole normalized impulse block occurs at exactly the multiples of one positive rank.
The rank is constructed in the finite unit group modulo scalar units. -/
theorem block_rank (E : LinearRecurrence ℤ) (hk : 2 ≤ E.order)
    (p : ℕ) (hp : p.Prime) (htrail : ¬ (p : ℤ) ∣ E.charPoly.coeff 0) :
    ∃ r : ℕ, 0 < r ∧ ∀ n : ℕ,
      (∀ j : Fin (E.order-1), (p : ℤ) ∣ impulse E (n+j.val)) ↔ r ∣ n := by
  letI : Fact p.Prime := ⟨hp⟩
  let zcast : ℤ →+* ZMod p := Int.castRingHom _
  let g : (ZMod p)[X] := E.charPoly.map zcast
  have hg : g.Monic := E.charPoly_monic.map zcast
  have hdeg : g.natDegree=E.order :=
    (E.charPoly_monic.natDegree_map zcast).trans
      (Polynomial.natDegree_eq_of_degree_eq_some E.charPoly_degree_eq_order)
  have h0 : g.coeff 0 ≠ 0 := by
    rw [show g.coeff 0 = zcast (E.charPoly.coeff 0) by simp only [g,Polynomial.coeff_map]]
    change (E.charPoly.coeff 0 : ZMod p) ≠ 0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).not.mpr htrail
  obtain ⟨r,hr,hh⟩ := finite_scalar_rank g hg (by rw [hdeg];exact hk) h0
  have hd (n : ℕ) :
      (∀ j : Fin (E.order-1), (p : ℤ) ∣ impulse E (n+j.val)) ↔
      ∀ i : Fin (E.order-1), (p : ℤ) ∣
        (AdjoinRoot.modByMonicHom E.charPoly_monic ((AdjoinRoot.root E.charPoly)^n)).coeff
          (E.order-1-i.val) := by
    rw [span_divisibility,block_coefficient_ideal E hk n,← span_divisibility]
  have hmap (n : ℕ) :
      AdjoinRoot.modByMonicHom hg ((AdjoinRoot.root g)^n) =
      (AdjoinRoot.modByMonicHom E.charPoly_monic ((AdjoinRoot.root E.charPoly)^n)).map zcast := by
    rw [powers_remainder,powers_remainder,Polynomial.map_modByMonic zcast E.charPoly_monic]
    simp only [g,Polynomial.map_pow,Polynomial.map_X]
  refine ⟨r,hr,?_⟩
  intro n
  rw [hd n,← hh n]
  rw [hmap n,hdeg]
  have hz (a : ℤ) : zcast a = 0 ↔ (p : ℤ) ∣ a :=
    ZMod.intCast_zmod_eq_zero_iff_dvd a p
  simp only [Polynomial.coeff_map,hz]

#print axioms block_rank

end D5.S3.Arith.LocalDold.QuotientBlock
