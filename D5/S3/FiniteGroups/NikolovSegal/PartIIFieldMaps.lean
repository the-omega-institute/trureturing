/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIIFieldMaps
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIIFieldMaps
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-field fixed-field estimates and quantitative semilinear sum surjectivity. -/

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Fixed
import Mathlib.Algebra.Ring.Action.End
import Mathlib.GroupTheory.GroupAction.FixedPoints
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
/-! Nikolov--Segal PartII pp257--259 Lemma7.1(a). The finite-field
surjective maps are proved here; no finite-simple CFSG or group PRODUCT
existence theorem is asserted. All field coefficients precede targets. -/
namespace NikolovSegal.PartIIFieldMaps
universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

-- Actual cardinal estimate used in PartII p258, Lemma7.1 Case3.
private theorem fixed_power_card_le (phi : RingAut F) (d : ℕ) (hd : 0 < d) :
    Nat.card (FixedBy.subfield F (phi^d)) ≤ (Nat.card (FixedBy.subfield F phi))^d := by
  classical
  let E := FixedBy.subfield F (phi^d)
  let K := FixedBy.subfield F phi
  have hcomm : ∀ x : F, (phi^d) (phi x) = phi ((phi^d) x) := by
    intro x
    change ((phi^d)*phi) x = (phi*(phi^d)) x
    rw [← pow_succ,← pow_succ']
  let alpha : RingAut E :=
    { toFun := fun x => ⟨phi x.val,by change (phi^d) (phi x.val) = phi x.val; rw [hcomm]; exact congrArg phi x.prop⟩
      invFun := fun x => ⟨phi.symm x.val,by
        change (phi^d) (phi.symm x.val) = phi.symm x.val
        apply phi.injective
        rw [← hcomm,RingEquiv.apply_symm_apply]
        exact x.prop⟩
      left_inv := fun x => Subtype.ext (phi.symm_apply_apply x.val)
      right_inv := fun x => Subtype.ext (phi.apply_symm_apply x.val)
      map_mul' := fun x y => Subtype.ext (map_mul phi x.val y.val)
      map_add' := fun x y => Subtype.ext (map_add phi x.val y.val) }
  have hpow : ∀ n (x : E), ((alpha^n) x).val = (phi^n) x.val := by
    intro n x
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [pow_succ',RingAut.mul_apply]
      change phi (((alpha^n) x).val) = phi ((phi^n) x.val)
      rw [ih]
  have halpha : alpha^d = 1 := by
    ext x
    exact (hpow d x).trans x.prop
  let G := Subgroup.zpowers alpha
  let R := FixedPoints.subfield G E
  letI : Finite G := Finite.of_equiv (Fin (orderOf alpha))
    (finEquivZPowers (isOfFinOrder_iff_pow_eq_one.mpr ⟨d,hd,halpha⟩))
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype R := Fintype.ofFinite R
  letI : Fintype E := Fintype.ofFinite E
  letI : Fintype K := Fintype.ofFinite K
  have hiter : ∀ (x : K), (phi^d) x.val = x.val := by
    intro x
    have hall : ∀ n : ℕ, (phi^n) x.val = x.val := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => simp only [pow_succ',RingAut.mul_apply,ih]; exact x.prop
    exact hall d
  let e : R ≃ K :=
    { toFun := fun x => ⟨x.val.val,by
        have hx := x.prop (⟨alpha,Subgroup.mem_zpowers alpha⟩ : G)
        exact congrArg Subtype.val hx⟩
      invFun := fun x => ⟨⟨x.val,hiter x⟩,by
        intro g
        have hx : (⟨x.val,hiter x⟩ : E) ∈ MulAction.fixedBy E alpha := by
          exact Subtype.ext x.prop
        obtain ⟨n,hn⟩ := Subgroup.mem_zpowers_iff.mp g.prop
        have hh := MulAction.mem_fixedBy_zpow hx n
        change (g.val) • (⟨x.val,hiter x⟩ : E) = _
        rw [← hn]
        exact hh⟩
      left_inv := fun x => Subtype.ext (Subtype.ext rfl)
      right_inv := fun x => Subtype.ext rfl }
  have hcard : Fintype.card R = Fintype.card K := Fintype.card_congr e
  have hfin := FixedPoints.finrank_eq_card G E
  have hG : Fintype.card G ≤ d := by
    change Fintype.card (Subgroup.zpowers alpha) ≤ d
    have horder : Fintype.card G = orderOf alpha := by
      exact (Fintype.card_congr (finEquivZPowers
        (isOfFinOrder_iff_pow_eq_one.mpr ⟨d,hd,halpha⟩))).symm.trans (Fintype.card_fin _)
    rw [horder]
    exact orderOf_le_of_pow_eq_one hd halpha
  simp only [Nat.card_eq_fintype_card]
  rw [Module.card_eq_pow_finrank (K := R) (V := E),hfin,hcard]
  exact pow_le_pow_right' (Fintype.card_pos) hG



private theorem mem_subfield_card (K : Subfield F) (x : F) :
    x ∈ K ↔ x^(Nat.card K) = x := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  let T := Finset.univ.filter (fun x : F => x^(Fintype.card K) = x)
  let A := Finset.univ.image (fun x : K => x.val)
  have hA : A.card = Fintype.card K := by
    simp only [A,Finset.card_image_of_injective _ Subtype.val_injective,Finset.card_univ]
  have hAT : A ⊆ T := by
    intro y hy
    obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hy
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    exact congrArg Subtype.val (FiniteField.pow_card z)
  have hT : T.card ≤ Fintype.card K := by
    have hz := FiniteField.X_pow_card_sub_X_ne_zero F (Fintype.one_lt_card (α := K))
    have hh := Polynomial.card_le_degree_of_subset_roots (p := Polynomial.X^(Fintype.card K)-Polynomial.X)
      (Z := T) (by
        intro z hzT
        rw [Polynomial.mem_roots hz,Polynomial.IsRoot]
        simp only [Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X]
        exact sub_eq_zero.mpr (Finset.mem_filter.mp hzT).2)
    simpa only [FiniteField.X_pow_card_sub_X_natDegree_eq F (Fintype.one_lt_card (α := K))] using hh
  have hATeq : A = T := Finset.eq_of_subset_of_card_le hAT (hT.trans_eq hA.symm)
  rw [Nat.card_eq_fintype_card]
  change x ∈ K ↔ x^Fintype.card K = x
  have hx : x ∈ T ↔ x^Fintype.card K = x := by simp [T]
  rw [← hx,← hATeq]
  simp only [A,Finset.mem_image,Finset.mem_univ,true_and]
  exact ⟨fun hx => ⟨⟨x,hx⟩,rfl⟩,fun ⟨z,hz⟩ => hz ▸ z.prop⟩

/-- Finite subfields inside the SAME field are determined by their actual
cardinality. This consumes the pinned finite-field root bound. -/
private theorem subfield_eq_of_card (K1 K2 : Subfield F) (h : Nat.card K1 = Nat.card K2) : K1 = K2 := by
  ext x
  rw [mem_subfield_card,mem_subfield_card,h]

-- The actual same-fixed-field inference in Lemma7.1 Case3.
private theorem same_fixed_card_power (phi1 phi2 : RingAut F)
    (h : Nat.card (FixedBy.subfield F phi1) = Nat.card (FixedBy.subfield F phi2)) :
    ∃ l : ℕ, phi1 = phi2^l := by
  classical
  letI : Finite (RingAut F) := Finite.of_injective (fun f : RingAut F => (⇑f : F → F)) DFunLike.coe_injective
  let G := Subgroup.zpowers phi2
  let R := FixedPoints.subfield G F
  have heq := subfield_eq_of_card (FixedBy.subfield F phi1) (FixedBy.subfield F phi2) h
  let A : F ≃ₐ[R] F :=
    { __ := phi1
      commutes' := fun x => by
        have hx2 : x.val ∈ FixedBy.subfield F phi2 := x.prop (⟨phi2,Subgroup.mem_zpowers phi2⟩ : G)
        rw [← heq] at hx2
        exact hx2 }
  obtain ⟨g,hg⟩ := FixedPoints.toAlgAut_surjective G F A
  have he : g.val = phi1 := by
    ext x
    exact DFunLike.congr_fun hg x
  have hp : phi1 ∈ Subgroup.zpowers phi2 := he ▸ g.prop
  obtain ⟨l,hl,he⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hp)
  exact ⟨l,he.symm⟩


/-- PartII equation(5)'s genuine automorphism orbit product. -/
def orbitProduct (phi : RingAut F) (d : ℕ) (a : F) : F :=
  ∏ i ∈ Finset.range d, (phi ^ i) a

def fieldValue (phi : RingAut F) (mu : F) (d c : ℕ) (a t : F) : F :=
  mu * (orbitProduct phi d a)^c * (phi^d) t - t

private theorem orbit_shift (phi : RingAut F) (d : ℕ) (a : F) :
    phi (orbitProduct phi d a) * a = (phi^d) a * orbitProduct phi d a := by
  induction d with
  | zero => simp [orbitProduct]
  | succ d ih =>
    have hnext : phi ((phi^d) a) = (phi^(d+1)) a := by rw [pow_succ',RingAut.mul_apply]
    simp only [orbitProduct,Finset.prod_range_succ,map_mul] at *
    rw [hnext]
    linear_combination ((phi^(d+1)) a) * ih

private theorem nontrivial_orbit_power (phi : RingAut F) (d c : ℕ) (hc : 0 < c)
    (hlarge : c*(Finset.univ.filter (fun t : F => (phi^d) t = t)).card < Fintype.card F) :
    ∃ a : F, a ≠ 0 ∧ (orbitProduct phi d a)^c ≠ 1 := by
  classical
  by_contra hn
  have hone : ∀ a : F, a ≠ 0 → (orbitProduct phi d a)^c = 1 := by
    simpa only [not_exists,not_and,not_not] using hn
  have hfix : ∀ a : F, (phi^d) (a^c) = a^c := by
    intro a
    by_cases ha : a = 0
    · simp [ha,hc.ne']
    have h := congrArg (fun z : F => z^c) (orbit_shift phi d a)
    simp only [mul_pow,← map_pow,hone a ha,map_one,mul_one,one_mul] at h
    exact h.symm
  have hp := FiniteField.card_image_polynomial_eval (R := F) (p := Polynomial.X^c)
    (by rw [Polynomial.degree_X_pow]; exact_mod_cast hc)
  have himage : (Finset.univ.image (fun a : F => a^c)) ⊆
      Finset.univ.filter (fun t : F => (phi^d) t = t) := by
    intro t ht
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp ht
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact hfix a
  simp only [Polynomial.natDegree_X_pow,Polynomial.eval_pow,Polynomial.eval_X] at hp
  exact (not_le_of_gt hlarge) (hp.trans (Nat.mul_le_mul_left c (Finset.card_le_card himage)))

private theorem sum_telescope (psi : RingAut F) (l : ℕ) (t : F) :
    psi (∑ i ∈ Finset.range l, (psi^i) t) - (∑ i ∈ Finset.range l, (psi^i) t) =
      (psi^l) t - t := by
  induction l with
  | zero => simp
  | succ l ih =>
    have hnext : psi ((psi^l) t) = (psi^(l+1)) t := by rw [pow_succ',RingAut.mul_apply]
    simp only [Finset.sum_range_succ,map_add,hnext]
    linear_combination ih

/-- The genuine two-summand Case3 of PartII Lemma7.1, pp258--259.
The quantitative hypothesis is the ACTUAL phi1^d fixed-field size, not a
surjectivity premise. Lambda is chosen before all targets. The companion
summand retains its prescribed independent mu2 and automorphism. -/
private theorem lemma7_1_two_summand
    (phi1 phi2 : RingAut F) (l d c1 c2 : ℕ) (hpower : phi1 = phi2^l)
    (b1 b2 : F) (hb1 : b1 ≠ 0) (hb2 : b2 ≠ 0) (hc1 : 0 < c1)
    (hlarge : c1*(Finset.univ.filter (fun t : F => (phi1^d) t = t)).card < Fintype.card F) :
    ∃ a : F, a ≠ 0 ∧ ∀ target : F, ∃ t1 t2 : F,
      fieldValue phi1 (b1 / (phi1^d) b1) d c1 a t1 +
      fieldValue phi2 (b2 / (phi2^d) b2) d c2 1 t2 = target := by
  classical
  let b := b1/b2
  have hb : b ≠ 0 := div_ne_zero hb1 hb2
  have hphi : phi1^d = (phi2^d)^l := by rw [hpower,← pow_mul,← pow_mul,Nat.mul_comm]
  obtain ⟨a,ha,haN⟩ := nontrivial_orbit_power phi1 d c1 hc1 hlarge
  have hchoose : ∃ a : F, a ≠ 0 ∧ b*(orbitProduct phi1 d a)^c1 - (phi1^d) b ≠ 0 := by
    by_cases hfix : (phi1^d) b = b
    · refine ⟨a,ha,?_⟩
      rw [hfix]
      intro hz
      have hh : b*(orbitProduct phi1 d a)^c1 = b*1 := by simpa using sub_eq_zero.mp hz
      exact haN (mul_left_cancel₀ hb hh)
    · exact ⟨1,one_ne_zero,by simpa [orbitProduct,sub_ne_zero] using Ne.symm hfix⟩
  obtain ⟨a,ha,hcoef⟩ := hchoose
  refine ⟨a,ha,?_⟩
  intro target
  let A := (orbitProduct phi1 d a)^c1
  let coeff := b*A - (phi1^d) b
  let t := (phi1^d).symm (target / (b2*coeff))
  let s := ∑ i ∈ Finset.range l, ((phi2^d)^i) (b*t)
  refine ⟨b1*t,-b2*s,?_⟩
  have h1 : (phi1^d) b1 ≠ 0 := (map_ne_zero (phi1^d)).mpr hb1
  have h2 : (phi2^d) b2 ≠ 0 := (map_ne_zero (phi2^d)).mpr hb2
  have htel : (phi2^d) s - s = (phi1^d) (b*t) - b*t := by
    simpa only [s,hphi] using sum_telescope (phi2^d) l (b*t)
  have hbt : b2*b = b1 := by dsimp [b]; field_simp
  have hv1 : fieldValue phi1 (b1/(phi1^d) b1) d c1 a (b1*t) = b1*(A*(phi1^d) t-t) := by
    dsimp [fieldValue,A]
    rw [map_mul]
    field_simp
  have hv2 : fieldValue phi2 (b2/(phi2^d) b2) d c2 1 (-b2*s) = -b2*((phi2^d) s-s) := by
    simp only [fieldValue,orbitProduct,map_one,Finset.prod_const_one,one_pow,mul_one,map_neg,map_mul]
    field_simp
    ring
  rw [hv1,hv2,htel,map_mul]
  calc
    _ = (b2*coeff)*(phi1^d) t := by dsimp [coeff]; linear_combination -(A*(phi1^d) t-t)*hbt
    _ = target := by
      simp only [t,RingEquiv.apply_symm_apply]
      exact mul_div_cancel₀ target (mul_ne_zero hb2 hcoef)


private theorem semilinear_surjective (psi : RingAut F) (A : F)
    (hzero : ∀ t : F, A * psi t - t = 0 → t = 0) :
    Function.Surjective (fun t : F => A*psi t-t) := by
  apply Finite.surjective_of_injective
  intro t s h
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub]
  linear_combination h

-- Actual Case2: choose a nonzero lambda by surjective finite-field norm;
-- no quotient, scalar surjectivity or target-dependent correction is assumed.
private theorem lemma7_1_large_fixed_field (phi : RingAut F) (d c : ℕ) (hd : 0 < d) (hc : 0 < c)
    (b : F) (hb : b ≠ 0)
    (hlarge : c*d < Nat.card (FixedBy.subfield F phi)-1) :
    ∃ a : F, a ≠ 0 ∧ Function.Surjective (fieldValue phi (b/(phi^d) b) d c a) := by
  classical
  let K := FixedBy.subfield F phi
  letI : Fintype K := Fintype.ofFinite K
  let A : F ≃ₐ[K] F :=
    { __ := phi
      commutes' := fun x => x.prop }
  have hpow : ∀ n x, (A^n) x = (phi^n) x := by
    intro n x
    induction n with
    | zero => rfl
    | succ n ih => simp only [pow_succ',AlgEquiv.mul_apply,RingAut.mul_apply]; exact congrArg phi ih
  have hnorm : ∀ n x, Algebra.norm K ((phi^n) x) = Algebra.norm K x := by
    intro n x
    rw [← hpow]
    exact Algebra.norm_eq_of_algEquiv (A^n) x
  obtain ⟨g,hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  obtain ⟨a,ha⟩ := FiniteField.unitsMap_norm_surjective K F g
  have haN : Algebra.norm K (a.val : F) = (g.val : K) := congrArg Units.val ha
  have hgne : (g.val : K)^(c*d) ≠ 1 := by
    intro he
    have hge : g^(c*d) = 1 := Units.ext he
    have hdiv : orderOf g ∣ c*d := orderOf_dvd_of_pow_eq_one hge
    have hcard : Nat.card Kˣ = Nat.card K-1 := Nat.card_units K
    rw [hg,hcard] at hdiv
    exact (not_le_of_gt hlarge) (Nat.le_of_dvd (Nat.mul_pos hc hd) hdiv)
  have hnormP : Algebra.norm K (orbitProduct phi d a.val) = (g.val : K)^d := by
    simp only [orbitProduct,map_prod,hnorm,haN,Finset.prod_const,Finset.card_range]
  have hnormb : Algebra.norm K b ≠ 0 := Algebra.norm_ne_zero_iff.mpr hb
  have hnormmu : Algebra.norm K (b/(phi^d) b) = 1 := by
    rw [div_eq_mul_inv,map_mul,Algebra.norm_inv,hnorm,mul_inv_cancel₀ hnormb]
  refine ⟨a.val,a.ne_zero,?_⟩
  apply semilinear_surjective
  intro t ht
  by_contra htn
  have hnormt : Algebra.norm K t ≠ 0 := Algebra.norm_ne_zero_iff.mpr htn
  have he : (b/(phi^d) b)*(orbitProduct phi d a.val)^c*(phi^d) t = t := sub_eq_zero.mp ht
  have hn := congrArg (Algebra.norm K (S := F)) he
  simp only [map_mul,map_pow,hnormmu,hnormP,hnorm,one_mul,← pow_mul] at hn
  have heq : (g.val : K)^(d*c) = 1 := by
    apply mul_right_cancel₀ hnormt
    simpa only [one_mul] using hn
  exact hgne (by simpa only [Nat.mul_comm] using heq)

private theorem fixed_card_filter (phi : RingAut F) :
    Nat.card (FixedBy.subfield F phi) = (Finset.univ.filter (fun x : F => phi x = x)).card := by
  classical
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype]
  congr 1
  ext x
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,FixedBy.subfield_mem_iff]
  rfl

private theorem field_non_coboundary (phi : RingAut F) (mu : F) (d c : ℕ)
    (hmu : ¬ ∃ b : F, b ≠ 0 ∧ mu = b/(phi^d) b) :
    Function.Surjective (fieldValue phi mu d c 1) := by
  have hz : ∀ t : F, mu*(phi^d) t-t = 0 → t = 0 := by
    intro t ht
    by_contra htn
    apply hmu
    refine ⟨t,htn,?_⟩
    exact (eq_div_iff ((map_ne_zero (phi^d)).mpr htn)).mpr (sub_eq_zero.mp ht)
  change Function.Surjective (fun t : F => fieldValue phi mu d c 1 t)
  simpa only [fieldValue,orbitProduct,map_one,Finset.prod_const_one,one_pow,mul_one] using
    semilinear_surjective (phi^d) mu hz

-- Extend a proved one-summand map to the genuine full prescribed sum,
-- setting all other witnesses to zero, while keeping every coefficient fixed.
private theorem lift_single_field_map {M : ℕ}
    (phi : Fin M → RingAut F) (mu : Fin M → F) (d c : Fin M → ℕ)
    (i : Fin M) (a : F) (ha : a ≠ 0)
    (hs : Function.Surjective (fieldValue (phi i) (mu i) (d i) (c i) a)) :
    ∃ lambda : Fin M → F, (∀ j, lambda j ≠ 0) ∧
      Function.Surjective (fun t : Fin M → F => ∑ j, fieldValue (phi j) (mu j) (d j) (c j) (lambda j) (t j)) := by
  classical
  let lambda : Fin M → F := fun j => if j=i then a else 1
  refine ⟨lambda,fun j => by dsimp [lambda]; split_ifs; exact ha; exact one_ne_zero,?_⟩
  intro target
  obtain ⟨v,hv⟩ := hs target
  let t : Fin M → F := fun j => if j=i then v else 0
  refine ⟨t,?_⟩
  change (∑ j, fieldValue (phi j) (mu j) (d j) (c j) (lambda j) (t j)) = target
  rw [Finset.sum_eq_single i]
  · simpa only [lambda,t,if_pos rfl] using hv
  · intro j _ hji
    simp [t,hji,fieldValue]
  · simp

private theorem lift_pair_field_map {M : ℕ}
    (phi : Fin M → RingAut F) (mu : Fin M → F) (d c : Fin M → ℕ)
    (i j : Fin M) (hij : i ≠ j) (a : F) (ha : a ≠ 0)
    (hs : ∀ target : F, ∃ v w : F,
      fieldValue (phi i) (mu i) (d i) (c i) a v + fieldValue (phi j) (mu j) (d j) (c j) 1 w = target) :
    ∃ lambda : Fin M → F, (∀ j, lambda j ≠ 0) ∧
      Function.Surjective (fun t : Fin M → F => ∑ j, fieldValue (phi j) (mu j) (d j) (c j) (lambda j) (t j)) := by
  classical
  let lambda : Fin M → F := fun k => if k=i then a else 1
  refine ⟨lambda,fun k => by dsimp [lambda]; split_ifs; exact ha; exact one_ne_zero,?_⟩
  intro target
  obtain ⟨v,w,hvw⟩ := hs target
  let t : Fin M → F := fun k => if k=i then v else if k=j then w else 0
  refine ⟨t,?_⟩
  change (∑ k, fieldValue (phi k) (mu k) (d k) (c k) (lambda k) (t k)) = target
  rw [Finset.sum_eq_add_of_mem i j (Finset.mem_univ _) (Finset.mem_univ _) hij]
  · simpa only [lambda,t,if_pos rfl,if_neg hij.symm,ite_true] using hvw
  · intro k _ hk
    simp [t,hk.1,hk.2,fieldValue]

/-- The full genuine quantitative Lemma7.1(a), PartII printed pp257--259.
M,q,c and the field cutoff precede all automorphism/divisor/coefficient tuples;
the nonzero lambda tuple precedes EVERY additive target. Case3's fixed-field
size and same-subgroup/power inference are DERIVED from actual finite fields.
This is a field-map theorem, not finite-simple scalar PRODUCT existence. -/
theorem lemma7_1 {q M c : ℕ} (hq : 0 < q)
    (hM : q*(c*q+1) < M) (hF : c*(c*q+1)^q < Fintype.card F)
    (phi : Fin M → RingAut F) (mu : Fin M → F) (d ci : Fin M → ℕ)
    (hmu : ∀ i, mu i ≠ 0) (hd : ∀ i, 0 < d i ∧ d i ∣ q)
    (hci : ∀ i, 0 < ci i ∧ ci i ≤ c) :
    ∃ lambda : Fin M → F, (∀ i, lambda i ≠ 0) ∧
      Function.Surjective (fun t : Fin M → F => ∑ i, fieldValue (phi i) (mu i) (d i) (ci i) (lambda i) (t i)) := by
  classical
  by_cases hbad : ∃ i : Fin M, ¬ ∃ b : F, b ≠ 0 ∧ mu i = b/(phi i^d i) b
  · obtain ⟨i,hi⟩ := hbad
    exact lift_single_field_map phi mu d ci i 1 one_ne_zero (field_non_coboundary (phi i) (mu i) (d i) (ci i) hi)
  have hb : ∀ i : Fin M, ∃ b : F, b ≠ 0 ∧ mu i = b/(phi i^d i) b := by
    intro i
    by_contra hi
    exact hbad ⟨i,hi⟩
  choose b hb hmb using hb
  have hdle : ∀ i, d i ≤ q := fun i => Nat.le_of_dvd hq (hd i).2
  by_cases hlarge : ∃ i : Fin M, c*q+1 < Nat.card (FixedBy.subfield F (phi i))
  · obtain ⟨i,hi⟩ := hlarge
    have hcd : ci i*d i < Nat.card (FixedBy.subfield F (phi i))-1 := by
      have hh := Nat.mul_le_mul (hci i).2 (hdle i)
      omega
    obtain ⟨a,ha,hs⟩ := lemma7_1_large_fixed_field (phi i) (d i) (ci i) (hd i).1 (hci i).1 (b i) (hb i) hcd
    apply lift_single_field_map phi mu d ci i a ha
    simpa only [← hmb i] using hs
  have hsmall : ∀ i, Nat.card (FixedBy.subfield F (phi i)) ≤ c*q+1 := by
    simpa only [not_exists,not_lt] using hlarge
  have hKpos : ∀ i, 0 < Nat.card (FixedBy.subfield F (phi i)) := fun i => Nat.card_pos
  let tag : Fin M → Fin (c*q+1) × Fin q := fun i =>
    (⟨Nat.card (FixedBy.subfield F (phi i))-1,by have hp := hKpos i; have hs := hsmall i; omega⟩,
     ⟨d i-1,by have hp := (hd i).1; have hle := hdle i; omega⟩)
  have htags : Fintype.card (Fin (c*q+1) × Fin q) < Fintype.card (Fin M) := by
    simpa only [Fintype.card_prod,Fintype.card_fin,Nat.mul_comm] using hM
  obtain ⟨i,j,ht,hij⟩ := Function.not_injective_iff.mp (Fintype.not_injective_of_card_lt tag htags)
  have hK : Nat.card (FixedBy.subfield F (phi i)) = Nat.card (FixedBy.subfield F (phi j)) := by
    have ht' := congrArg (fun z => z.1.val) ht
    dsimp [tag] at ht'
    have hi := hKpos i; have hj := hKpos j
    omega
  have hdij : d i = d j := by
    have ht' := congrArg (fun z => z.2.val) ht
    dsimp [tag] at ht'
    have hi := (hd i).1; have hj := (hd j).1
    omega
  obtain ⟨l,hl⟩ := same_fixed_card_power (phi i) (phi j) hK
  have hfixed := fixed_power_card_le (phi i) (d i) (hd i).1
  have hpow : Nat.card (FixedBy.subfield F (phi i^d i)) ≤ (c*q+1)^q := by
    exact hfixed.trans ((Nat.pow_le_pow_left (hsmall i) (d i)).trans
      (pow_le_pow_right' (by omega) (hdle i)))
  have hf : ci i*(Finset.univ.filter (fun t : F => (phi i^d i) t = t)).card < Fintype.card F := by
    rw [← fixed_card_filter]
    exact (Nat.mul_le_mul (hci i).2 hpow).trans_lt hF
  obtain ⟨a,ha,hs⟩ := lemma7_1_two_summand (phi i) (phi j) l (d i) (ci i) (ci j) hl (b i) (b j) (hb i) (hb j) (hci i).1 hf
  apply lift_pair_field_map phi mu d ci i j hij a ha
  intro target
  obtain ⟨v,w,hvw⟩ := hs target
  have hmbj : mu j = b j/(phi j^d i) (b j) := by rw [hdij]; exact hmb j
  rw [← hmb i,← hmbj] at hvw
  exact ⟨v,w,by simpa only [hdij] using hvw⟩

end NikolovSegal.PartIIFieldMaps
