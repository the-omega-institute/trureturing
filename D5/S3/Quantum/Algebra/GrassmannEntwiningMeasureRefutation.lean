/- GID: D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.claim; result=D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.result; claim=D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.claim
   digest: The Gamma(3) coefficient Jacobian refutes the conjectured density for S. -/

import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.LinearAlgebra.Determinant

set_option autoImplicit false
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.longLine false

namespace D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation

open scoped BigOperators

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

private abbrev Mon := Finset (Fin 3)
private abbrev G := ExteriorAlgebra ℝ (Fin 3 → ℝ)
private abbrev C := Mon → ℝ
private abbrev X := (Mon × Fin 4) → ℝ

noncomputable def monomialBasis : Module.Basis Mon ℝ G :=
  (Pi.basisFun ℝ (Fin 3)).ExteriorAlgebra

noncomputable def coord : G ≃ₗ[ℝ] C := monomialBasis.equivFun

noncomputable def unitC : C := coord 1

noncomputable def gmul (u v : C) : C := coord (coord.symm u * coord.symm v)

private lemma monomialBasis_empty : monomialBasis ∅ = 1 := by
  rw [monomialBasis, ExteriorAlgebra.basis_apply_ofCard
    (Pi.basisFun ℝ (Fin 3)) (Finset.card_empty)]
  exact ExteriorAlgebra.ιMulti_zero_apply _

private lemma unitC_apply (s : Mon) : unitC s = if s = ∅ then 1 else 0 := by
  rw [unitC, ← monomialBasis_empty]
  simp only [coord.eq_1, Module.Basis.equivFun_self, eq_comm]

private lemma decode_gmul (u v : C) :
    coord.symm (gmul u v) = coord.symm u * coord.symm v :=
  coord.symm_apply_apply _

private lemma gmul_scalar_left (c : ℝ) (u : C) : gmul (c • unitC) u = c • u := by
  apply coord.symm.injective
  rw [decode_gmul]
  simp [unitC, map_smul]

private lemma gmul_scalar_right (c : ℝ) (u : C) : gmul u (c • unitC) = c • u := by
  apply coord.symm.injective
  rw [decode_gmul]
  simp [unitC, map_smul]

private lemma gmul_unit_left (u : C) : gmul unitC u = u := by
  simpa using gmul_scalar_left 1 u

private lemma gmul_unit_right (u : C) : gmul u unitC = u := by
  simpa using gmul_scalar_right 1 u

private lemma monomial_overlap_zero (s t : Mon) (h : ¬ Disjoint s t) :
    monomialBasis s * monomialBasis t = 0 :=
  ExteriorAlgebra.basis_mul_of_not_disjoint (Pi.basisFun ℝ (Fin 3))
    (Set.powersetCard.ofCard (rfl : s.card = s.card))
    (Set.powersetCard.ofCard (rfl : t.card = t.card)) h

private lemma monomial_product_wrong_parity (s t r : Mon)
    (h : r.card % 2 ≠ (s.card + t.card) % 2) :
    coord (monomialBasis s * monomialBasis t) r = 0 := by
  by_cases hd : Disjoint s t
  · have hm := ExteriorAlgebra.basis_mul_of_disjoint (Pi.basisFun ℝ (Fin 3))
      (Set.powersetCard.ofCard (rfl : s.card = s.card))
      (Set.powersetCard.ofCard (rfl : t.card = t.card)) hd
    change monomialBasis s * monomialBasis t =
      (_ : ℤˣ) • monomialBasis (s.disjUnion t hd) at hm
    rw [hm, map_zsmul_unit]
    simp only [Pi.smul_apply, coord.eq_1, Module.Basis.equivFun_self]
    rw [if_neg, smul_zero]
    intro he
    apply h
    rw [← he, Finset.card_disjUnion]
  · rw [monomial_overlap_zero s t hd, map_zero]
    rfl

private lemma gmul_expansion (u v : C) :
    gmul u v = ∑ s : Mon, ∑ t : Mon,
      (u s * v t) • coord (monomialBasis s * monomialBasis t) := by
  simp only [gmul.eq_1, coord.eq_1, Module.Basis.equivFun_symm_apply, Finset.sum_mul,
    Finset.mul_sum, smul_mul_smul_comm, map_sum, map_smul]
  rw [Finset.sum_comm]

private def HasParity (p : ℕ) (u : C) : Prop :=
  ∀ s : Mon, s.card % 2 ≠ p → u s = 0

noncomputable def ginv (u : C) : C :=
  (u ∅)⁻¹ • unitC - ((u ∅)⁻¹)^2 • (u - (u ∅) • unitC)

private lemma parity_add {p : ℕ} {u v : C}
    (hu : HasParity p u) (hv : HasParity p v) : HasParity p (u + v) := by
  intro s hs
  simp [hu s hs, hv s hs]

private lemma parity_sub {p : ℕ} {u v : C}
    (hu : HasParity p u) (hv : HasParity p v) : HasParity p (u - v) := by
  intro s hs
  simp [hu s hs, hv s hs]

private lemma parity_smul {p : ℕ} {u : C}
    (hu : HasParity p u) (c : ℝ) : HasParity p (c • u) := by
  intro s hs
  simp [hu s hs]

private lemma parity_unitC : HasParity 0 unitC := by
  intro s hs
  rw [unitC_apply, if_neg]
  intro he
  simp [he] at hs

private lemma parity_gmul {p q : ℕ} {u v : C}
    (hu : HasParity p u) (hv : HasParity q v) :
    HasParity ((p + q) % 2) (gmul u v) := by
  intro r hr
  rw [gmul_expansion]
  simp only [Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_eq_zero
  intro s _
  apply Finset.sum_eq_zero
  intro t _
  by_cases hs : s.card % 2 = p
  · by_cases ht : t.card % 2 = q
    · rw [monomial_product_wrong_parity s t r (by simpa [Nat.add_mod, hs, ht] using hr)]
      simp
    · simp [hv t ht]
  · simp [hu s hs]

private lemma even_nonempty_overlap : ∀ s t : Mon,
    s.card % 2 = 0 → t.card % 2 = 0 → s ≠ ∅ → t ≠ ∅ → ¬ Disjoint s t := by
  decide

private lemma even_nilpotent_part_sq (u : C) (hu : HasParity 0 u) :
    gmul (u - (u ∅) • unitC) (u - (u ∅) • unitC) = 0 := by
  rw [gmul_expansion]
  apply Finset.sum_eq_zero
  intro s _
  apply Finset.sum_eq_zero
  intro t _
  by_cases hs : s = ∅
  · simp [hs, unitC_apply]
  · by_cases ht : t = ∅
    · simp [ht, unitC_apply]
    · by_cases hp : s.card % 2 = 0
      · by_cases hq : t.card % 2 = 0
        · rw [monomial_overlap_zero s t (even_nonempty_overlap s t hp hq hs ht), map_zero]
          simp
        · simp [Pi.sub_apply, Pi.smul_apply, hu t hq, unitC_apply, ht]
      · simp [Pi.sub_apply, Pi.smul_apply, hu s hp, unitC_apply, hs]

private lemma parity_ginv (u : C) (hu : HasParity 0 u) : HasParity 0 (ginv u) :=
  parity_sub (parity_smul parity_unitC _) (parity_smul
    (parity_sub hu (parity_smul parity_unitC _)) _)

private noncomputable def coeffEval (s : Mon) : C →L[ℝ] ℝ :=
  ContinuousLinearMap.proj s

private noncomputable def mulB : C →L[ℝ] C →L[ℝ] C :=
  ∑ s : Mon, (coeffEval s).smulRight
    (∑ t : Mon, (coeffEval t).smulRight (coord (monomialBasis s * monomialBasis t)))

private lemma mulB_apply (u v : C) : mulB u v = gmul u v := by
  rw [gmul_expansion]
  simp [mulB.eq_1, coeffEval.eq_1, Finset.smul_sum, smul_smul]

private lemma gmul_ginv (u : C) (hu : HasParity 0 u) (hc : u ∅ ≠ 0) :
    gmul u (ginv u) = unitC := by
  let c := u ∅
  let N := u - c • unitC
  have he : u = c • unitC + N := (add_sub_cancel (c • unitC) u).symm
  have hn : mulB N N = 0 := by
    rw [mulB_apply]
    exact even_nilpotent_part_sq u hu
  have hp : mulB u N = c • N := by
    calc
      mulB u N = mulB (c • unitC + N) N := congrArg (fun v => mulB v N) he
      _ = c • N := by
        simp only [map_add, add_apply, hn, add_zero,
          mulB_apply, gmul_scalar_left]
  rw [← mulB_apply]
  change mulB u (c⁻¹ • unitC - (c⁻¹)^2 • N) = unitC
  rw [map_sub, map_smul, map_smul, hp, mulB_apply, gmul_unit_right]
  ext s
  dsimp [N, c]
  (field_simp [hc]; ring)

private lemma ginv_gmul (u : C) (hu : HasParity 0 u) (hc : u ∅ ≠ 0) :
    gmul (ginv u) u = unitC := by
  rw [← gmul_ginv u hu hc]
  simp only [← mulB_apply, ginv.eq_1, map_sub, map_smul,
    sub_apply, smul_apply]
  simp only [mulB_apply, gmul_unit_left, gmul_unit_right]

noncomputable def pick (p : ℕ) (j : Fin 4) : X →L[ℝ] C :=
  ContinuousLinearMap.pi fun s =>
    if s.card % 2 = p then ContinuousLinearMap.proj (s, j) else 0

def pack (e o : Fin 4 → C) : X :=
  fun i => if i.1.card % 2 = 0 then e i.2 i.1 else o i.2 i.1

noncomputable def ratio (z : X) : C := gmul (pick 0 2 z) (ginv (pick 0 0 z))

noncomputable def evenOut (a b : ℝ) (z : X) : Fin 4 → C :=
  let x1 := pick 0 0 z
  let x2 := pick 0 1 z
  let y1 := pick 0 2 z
  let y2 := pick 0 3 z
  let chi1 := pick 1 0 z
  let chi2 := pick 1 1 z
  let psi1 := pick 1 2 z
  let psi2 := pick 1 3 z
  ![gmul (gmul (gmul y1 y1) (unitC + gmul chi1 psi2)) (ginv (b • x1))
      + b⁻¹ • gmul y1 (y2 - a • unitC - gmul psi1 psi2),
    b • ginv y1, x1, a • unitC + gmul x1 x2 - ratio z + gmul chi1 chi2]

noncomputable def oddOut (z : X) : Fin 4 → C :=
  ![pick 1 2 z - gmul (ratio z) (pick 1 0 z), pick 1 3 z,
    pick 1 0 z, pick 1 1 z + gmul (ratio z) (pick 1 3 z)]

noncomputable def F (a b : ℝ) (z : X) : X := pack (evenOut a b z) (oddOut z)

def domain (z : X) : Prop := z (∅, 0) ≠ 0 ∧ z (∅, 2) ≠ 0

noncomputable def m (z : X) : ℝ := (z (∅, 2) ^ 3)⁻¹

noncomputable def jacobian (a b : ℝ) (z : X) : ℝ :=
  LinearMap.det (fderiv ℝ (F a b) z).toLinearMap

def claim : Prop :=
  ∀ z : X, domain z →
    jacobian 1 2 z = m z / m (F 1 2 z)

private lemma parity_pick (p : ℕ) (j : Fin 4) (z : X) : HasParity p (pick p j z) := by
  intro s hs
  simp [pick.eq_1, hs]

private lemma outputs_have_parity (a b : ℝ) (z : X) :
    (∀ j, HasParity 0 (evenOut a b z j)) ∧ (∀ j, HasParity 1 (oddOut z j)) := by
  have he := fun j => parity_pick 0 j z
  have ho := fun j => parity_pick 1 j z
  have hr : HasParity 0 (ratio z) := parity_gmul (he 2) (parity_ginv _ (he 0))
  constructor <;> intro j <;> fin_cases j <;> dsimp [evenOut.eq_1, oddOut.eq_1]
  · exact parity_add (parity_gmul (parity_gmul (parity_gmul (he 2) (he 2))
      (parity_add parity_unitC (parity_gmul (ho 0) (ho 3))))
      (parity_ginv _ (parity_smul (he 0) b))) (parity_smul
      (parity_gmul (he 2) (parity_sub (parity_sub (he 3)
        (parity_smul parity_unitC a)) (parity_gmul (ho 2) (ho 3)))) b⁻¹)
  · exact parity_smul (parity_ginv _ (he 2)) b
  · exact he 0
  · exact parity_add (parity_sub (parity_add (parity_smul parity_unitC a)
      (parity_gmul (he 0) (he 1))) hr) (parity_gmul (ho 0) (ho 1))
  · exact parity_sub (ho 2) (parity_gmul hr (ho 0))
  · exact ho 3
  · exact ho 0
  · exact parity_add (ho 1) (parity_gmul hr (ho 3))

private lemma pick_pack (e o : Fin 4 → C)
    (he : ∀ j, HasParity 0 (e j)) (ho : ∀ j, HasParity 1 (o j)) :
    (∀ j, pick 0 j (pack e o) = e j) ∧ (∀ j, pick 1 j (pack e o) = o j) := by
  constructor <;> intro j <;> ext s <;> by_cases hs : s.card % 2 = 0
  · simp [pick.eq_1, pack.eq_1, hs]
  · simp [pick.eq_1, hs, he j s hs]
  · simp [pick.eq_1, hs, ho j s (Nat.mod_two_ne_one.mpr hs)]
  · have hs1 : s.card % 2 = 1 := Nat.mod_two_ne_zero.mp hs
    simp [pick.eq_1, pack.eq_1, hs1]

private lemma pick_F (a b : ℝ) (z : X) :
    (∀ j, pick 0 j (F a b z) = evenOut a b z j) ∧
    (∀ j, pick 1 j (F a b z) = oddOut z j) :=
  pick_pack _ _ (outputs_have_parity a b z).1 (outputs_have_parity a b z).2

private lemma F_y_scalar (a b : ℝ) (z : X) : F a b z (∅, 2) = z (∅, 0) := by
  have h := congrFun ((pick_F a b z).1 2) ∅
  simpa [pick.eq_1, evenOut.eq_1] using h

private lemma isOpen_domain : IsOpen {z : X | domain z} :=
  (isOpen_ne_fun (continuous_apply (∅, 0)) continuous_const).inter
    (isOpen_ne_fun (continuous_apply (∅, 2)) continuous_const)

private lemma hasFDerivAt_gmul
    {f g : X → C} {f' g' : X →L[ℝ] C} {z : X}
    (hf : HasFDerivAt f f' z) (hg : HasFDerivAt g g' z) :
    HasFDerivAt (fun w => gmul (f w) (g w))
      (mulB.precompR X (f z) g' + mulB.precompL X f' (g z)) z := by
  simpa only [mulB_apply] using mulB.hasFDerivAt_of_bilinear hf hg

private lemma hasFDerivAt_gmul_scalar
    {f g : X → C} {f' g' : X →L[ℝ] C} {z : X}
    (hf : HasFDerivAt f f' z) (hg : HasFDerivAt g g' z)
    (c d : ℝ) (hfc : f z = c • unitC) (hgd : g z = d • unitC) :
    HasFDerivAt (fun w => gmul (f w) (g w)) (c • g' + d • f') z := by
  convert! hasFDerivAt_gmul hf hg using 1
  ext h
  simp [hfc, hgd, mulB_apply, gmul_unit_left, gmul_unit_right]

set_option maxHeartbeats 800000 in
-- The composed inverse derivative is normalized on eight coefficient coordinates.
private lemma hasFDerivAt_ginv_scalar (c : ℝ) (hc : c ≠ 0) :
    HasFDerivAt ginv (-((c⁻¹)^2) • ContinuousLinearMap.id ℝ C) (c • unitC) := by
  have he := (coeffEval ∅).hasFDerivAt (x := c • unitC)
  have hi := (hasFDerivAt_inv (by simpa [coeffEval.eq_1, unitC_apply] using hc)).comp
    (c • unitC) he
  have hn := (hasFDerivAt_id (𝕜 := ℝ) (c • unitC)).sub (he.smul_const unitC)
  convert! (hi.smul_const unitC).sub ((hi.mul hi).smul hn) using 1
  · ext u s
    simp [ginv.eq_1, coeffEval.eq_1, pow_two]
  · ext h s
    by_cases hs : s = ∅ <;>
      simp [coeffEval.eq_1, unitC_apply, pow_two, mul_inv_rev,
        ContinuousLinearMap.toSpanSingleton_apply, hs]
    all_goals ring

private lemma ginv_scalar (c : ℝ) (hc : c ≠ 0) : ginv (c • unitC) = c⁻¹ • unitC := by
  have h := ginv_gmul (c • unitC) (parity_smul parity_unitC c)
    (by simpa [unitC_apply] using hc)
  rw [gmul_scalar_right] at h
  calc
    ginv (c • unitC) = c⁻¹ • (c • ginv (c • unitC)) := by simp [smul_smul, hc]
    _ = c⁻¹ • unitC := by rw [h]

private lemma hasFDerivAt_ginv_comp
    {f : X → C} {f' : X →L[ℝ] C} {z : X}
    (hf : HasFDerivAt f f' z) (c : ℝ) (hc : c ≠ 0) (hfc : f z = c • unitC) :
    HasFDerivAt (fun w => ginv (f w)) (-((c⁻¹)^2) • f') z := by
  have hi := hasFDerivAt_ginv_scalar c hc
  rw [← hfc] at hi
  simpa using hi.comp z hf

private noncomputable def z0 : X :=
  fun i => if i.1 = ∅ then (![1, 3, 2, 4] : Fin 4 → ℝ) i.2 else 0

private lemma pick_even_z0 (j : Fin 4) :
    pick 0 j z0 = ((![1, 3, 2, 4] : Fin 4 → ℝ) j) • unitC := by
  ext s
  by_cases hs : s = ∅
  · simp [pick.eq_1, z0.eq_1, unitC_apply, hs]
  · by_cases hp : s.card % 2 = 0 <;> simp [pick.eq_1, z0.eq_1, unitC_apply, hs, hp]

private lemma pick_odd_z0 (j : Fin 4) : pick 1 j z0 = 0 := by
  ext s
  by_cases hs : s = ∅
  · simp [pick.eq_1, hs]
  · by_cases hp : s.card % 2 = 1 <;> simp [pick.eq_1, z0.eq_1, hs, hp]

private lemma z0_mem_domain : domain z0 := by norm_num [domain.eq_1, z0.eq_1]

private noncomputable def evenD : Fin 4 → (X →L[ℝ] C) :=
  ![(-2 : ℝ) • pick 0 0 + (7/2 : ℝ) • pick 0 2 + pick 0 3,
    (-1/2 : ℝ) • pick 0 2, pick 0 0,
    (5 : ℝ) • pick 0 0 + pick 0 1 - pick 0 2]

private noncomputable def oddD : Fin 4 → (X →L[ℝ] C) :=
  ![(-2 : ℝ) • pick 1 0 + pick 1 2, pick 1 3,
    pick 1 0, pick 1 1 + (2 : ℝ) • pick 1 3]

private lemma jet_gmul {f g : X → C} {f' g' : X →L[ℝ] C} {c d : ℝ}
    (hf : HasFDerivAt f f' z0 ∧ f z0 = c • unitC)
    (hg : HasFDerivAt g g' z0 ∧ g z0 = d • unitC) :
    HasFDerivAt (fun w => gmul (f w) (g w)) (c • g' + d • f') z0 ∧
      gmul (f z0) (g z0) = (c * d) • unitC :=
  ⟨hasFDerivAt_gmul_scalar hf.1 hg.1 c d hf.2 hg.2,
    by rw [hf.2, hg.2, gmul_scalar_left, smul_smul]⟩

private lemma jet_add {f g : X → C} {f' g' : X →L[ℝ] C} {c d : ℝ}
    (hf : HasFDerivAt f f' z0 ∧ f z0 = c • unitC)
    (hg : HasFDerivAt g g' z0 ∧ g z0 = d • unitC) :
    HasFDerivAt (f + g) (f' + g') z0 ∧ f z0 + g z0 = (c + d) • unitC :=
  ⟨hf.1.add hg.1, by rw [hf.2, hg.2, add_smul]⟩

private lemma jet_sub {f g : X → C} {f' g' : X →L[ℝ] C} {c d : ℝ}
    (hf : HasFDerivAt f f' z0 ∧ f z0 = c • unitC)
    (hg : HasFDerivAt g g' z0 ∧ g z0 = d • unitC) :
    HasFDerivAt (f - g) (f' - g') z0 ∧ f z0 - g z0 = (c - d) • unitC :=
  ⟨hf.1.sub hg.1, by rw [hf.2, hg.2, sub_smul]⟩

private lemma jet_smul {f : X → C} {f' : X →L[ℝ] C} {c : ℝ}
    (a : ℝ) (hf : HasFDerivAt f f' z0 ∧ f z0 = c • unitC) :
    HasFDerivAt (a • f) (a • f') z0 ∧ a • f z0 = (a * c) • unitC :=
  ⟨hf.1.const_smul a, by rw [hf.2, smul_smul]⟩

private lemma jet_ginv {f : X → C} {f' : X →L[ℝ] C} {c : ℝ}
    (hf : HasFDerivAt f f' z0 ∧ f z0 = c • unitC) (hc : c ≠ 0) :
    HasFDerivAt (fun w => ginv (f w)) (-((c⁻¹)^2) • f') z0 ∧
      ginv (f z0) = c⁻¹ • unitC :=
  ⟨hasFDerivAt_ginv_comp hf.1 c hc hf.2, by rw [hf.2, ginv_scalar c hc]⟩

private lemma jet_const (c : ℝ) :
    HasFDerivAt (fun _ : X => c • unitC) (0 : X →L[ℝ] C) z0 ∧
      c • unitC = c • unitC :=
  ⟨hasFDerivAt_const _ z0, rfl⟩

private lemma jet_even_pick (j : Fin 4) :
    HasFDerivAt (pick 0 j) (pick 0 j) z0 ∧
      pick 0 j z0 = ((![1, 3, 2, 4] : Fin 4 → ℝ) j) • unitC :=
  ⟨(pick 0 j).hasFDerivAt, pick_even_z0 j⟩

private lemma jet_odd_pick (j : Fin 4) :
    HasFDerivAt (pick 1 j) (pick 1 j) z0 ∧ pick 1 j z0 = (0 : ℝ) • unitC :=
  ⟨(pick 1 j).hasFDerivAt, by simp [pick_odd_z0]⟩

private lemma ratio_jet : ratio z0 = (2 : ℝ) • unitC ∧
    HasFDerivAt ratio ((-2 : ℝ) • pick 0 0 + pick 0 2) z0 := by
  have h := jet_gmul (jet_even_pick 2) (jet_ginv (jet_even_pick 0) (by norm_num))
  refine ⟨by simpa [ratio.eq_1] using h.2, ?_⟩
  convert! h.1 using 1
  ext v s
  norm_num [ratio.eq_1]

set_option maxHeartbeats 800000 in
-- Four composed output derivatives require finite linear-map normalization.
private lemma hasFDerivAt_evenOut :
    HasFDerivAt (evenOut 1 2) (ContinuousLinearMap.pi evenD) z0 := by
  apply hasFDerivAt_pi.mpr
  intro j
  fin_cases j
  · have hyy := jet_gmul (jet_even_pick 2) (jet_even_pick 2)
    have hcp := jet_gmul (jet_odd_pick 0) (jet_odd_pick 3)
    have hpp := jet_gmul (jet_odd_pick 2) (jet_odd_pick 3)
    have htop := jet_gmul hyy (jet_add (jet_const 1) hcp)
    have hi := jet_ginv (jet_smul 2 (jet_even_pick 0)) (by norm_num)
    have hleft := jet_gmul htop hi
    have hright := jet_smul (2 : ℝ)⁻¹ (jet_gmul (jet_even_pick 2)
      (jet_sub (jet_sub (jet_even_pick 3) (jet_const 1)) hpp))
    refine ((jet_add hleft hright).1.congr_fderiv ?_).congr_of_eventuallyEq ?_
    · ext h s
      (norm_num [evenD.eq_1]; ring)
    · exact Filter.Eventually.of_forall fun z => by simp [evenOut.eq_1]
  · refine ((jet_smul 2 (jet_ginv (jet_even_pick 2) (by norm_num))).1.congr_fderiv
      ?_).congr_of_eventuallyEq ?_
    · ext h s
      norm_num [evenD.eq_1, smul_smul]
    · exact Filter.Eventually.of_forall fun z => by simp [evenOut.eq_1]
  · simpa [evenOut.eq_1, evenD.eq_1] using (jet_even_pick 0).1
  · have hxx := jet_gmul (jet_even_pick 0) (jet_even_pick 1)
    have hcc := jet_gmul (jet_odd_pick 0) (jet_odd_pick 1)
    refine ((jet_add (jet_sub (jet_add (jet_const 1) hxx) ratio_jet.symm)
      hcc).1.congr_fderiv ?_).congr_of_eventuallyEq ?_
    · ext h s
      (simp [evenD.eq_1]; ring)
    · exact Filter.Eventually.of_forall fun z => by simp [evenOut.eq_1]

private lemma hasFDerivAt_oddOut :
    HasFDerivAt oddOut (ContinuousLinearMap.pi oddD) z0 := by
  apply hasFDerivAt_pi.mpr
  intro j
  fin_cases j
  · convert! (jet_sub (jet_odd_pick 2) (jet_gmul ratio_jet.symm (jet_odd_pick 0))).1 using 1
    ext h s
    (simp [oddD.eq_1]; ring)
  · simpa [oddOut.eq_1, oddD.eq_1] using (jet_odd_pick 3).1
  · simpa [oddOut.eq_1, oddD.eq_1] using (jet_odd_pick 0).1
  · convert! (jet_add (jet_odd_pick 1) (jet_gmul ratio_jet.symm (jet_odd_pick 3))).1 using 1
    ext h s
    simp [oddD.eq_1]

private noncomputable def evenBlock : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-2, 0, 7/2, 1; 0, 0, -1/2, 0; 1, 0, 0, 0; 5, 1, -1, 0]

private noncomputable def oddBlock : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-2, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 2]

private noncomputable def block (s : Mon) : Matrix (Fin 4) (Fin 4) ℝ :=
  if s.card % 2 = 0 then evenBlock else oddBlock

private noncomputable def L : X →L[ℝ] X :=
  ContinuousLinearMap.pi fun i =>
    ∑ j : Fin 4, block i.1 i.2 j • ContinuousLinearMap.proj (i.1, j)

set_option maxHeartbeats 800000 in
-- The eight block rows are normalized after parity and slot case splits.
private lemma packed_derivative_eq_L :
    ContinuousLinearMap.pi (fun i : Mon × Fin 4 =>
      (coeffEval i.1).comp
        (if i.1.card % 2 = 0 then evenD i.2 else oddD i.2)) = L := by
  ext h i
  rcases i with ⟨s, i⟩
  by_cases hs : s.card % 2 = 0
  · fin_cases i <;>
      simp [L.eq_1, block.eq_1, hs, evenBlock.eq_1, evenD.eq_1,
        coeffEval.eq_1, pick.eq_1, Fin.sum_univ_succ] <;> ring
  · have hs1 : s.card % 2 = 1 := Nat.mod_two_ne_zero.mp hs
    fin_cases i <;>
      simp [L.eq_1, block.eq_1, hs1, oddBlock.eq_1, oddD.eq_1,
        coeffEval.eq_1, pick.eq_1, Fin.sum_univ_succ]

private lemma hasFDerivAt_F_z0 : HasFDerivAt (F 1 2) L z0 := by
  rw [← packed_derivative_eq_L]
  apply HasFDerivWithinAt.hasFDerivAt (s := {z | domain z}) _
    (isOpen_domain.mem_nhds z0_mem_domain)
  apply HasFDerivAt.hasFDerivWithinAt
  apply hasFDerivAt_pi.mpr
  intro i
  by_cases hs : i.1.card % 2 = 0
  · simpa [F.eq_1, pack.eq_1, hs, coeffEval.eq_1, Function.comp_def] using
      (coeffEval i.1).hasFDerivAt.comp z0
        ((hasFDerivAt_pi.mp hasFDerivAt_evenOut) i.2)
  · simpa [F.eq_1, pack.eq_1, hs, coeffEval.eq_1, Function.comp_def] using
      (coeffEval i.1).hasFDerivAt.comp z0
        ((hasFDerivAt_pi.mp hasFDerivAt_oddOut) i.2)

private lemma toMatrix_L : LinearMap.toMatrix' L.toLinearMap =
    Matrix.reindex (Equiv.prodComm (Fin 4) Mon) (Equiv.prodComm (Fin 4) Mon)
      (Matrix.blockDiagonal block) := by
  ext i j
  rcases i with ⟨s, i⟩
  rcases j with ⟨t, j⟩
  by_cases hs : s = t
  · subst t
    simp [LinearMap.toMatrix'_apply, L.eq_1, Matrix.reindex_apply,
      Matrix.blockDiagonal, Pi.single_apply, eq_comm]
  · simp [LinearMap.toMatrix'_apply, L.eq_1, Matrix.reindex_apply,
      Matrix.blockDiagonal, hs]

private lemma det_evenBlock : Matrix.det evenBlock = (1/2 : ℝ) := by
  rw [Matrix.det_succ_row evenBlock 1]
  norm_num [evenBlock.eq_1, Fin.sum_univ_succ]
  change Matrix.det (!![-2, 0, 1; 1, 0, 0; 5, 1, 0] : Matrix (Fin 3) (Fin 3) ℝ) = 1
  norm_num [Matrix.det_fin_three]

private lemma det_oddBlock : Matrix.det oddBlock = (1 : ℝ) := by
  rw [Matrix.det_succ_row oddBlock 1]
  norm_num [oddBlock.eq_1, Fin.sum_univ_succ]
  change Matrix.det (!![-2, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) ℝ) = 1
  norm_num [Matrix.det_fin_three]

private lemma even_monomial_count :
    (Finset.univ.filter (fun s : Mon => s.card % 2 = 0)).card = 4 := by decide

private lemma det_L : LinearMap.det L.toLinearMap = (1/16 : ℝ) := by
  rw [← LinearMap.det_toMatrix', toMatrix_L, Matrix.det_reindex_self,
    Matrix.det_blockDiagonal]
  simp only [block.eq_1]
  simp_rw [apply_ite Matrix.det, det_evenBlock, det_oddBlock]
  rw [Finset.prod_ite]
  simp [Finset.prod_const, even_monomial_count]
  norm_num

private lemma jacobian_z0 : jacobian 1 2 z0 = (1/16 : ℝ) := by
  rw [jacobian, hasFDerivAt_F_z0.fderiv, det_L]

private lemma density_ratio_z0 : m z0 / m (F 1 2 z0) = (1/8 : ℝ) := by
  rw [m, m, F_y_scalar]
  norm_num [z0.eq_1]

theorem result : ¬ claim := by
  intro h
  have h0 := h z0 z0_mem_domain
  rw [jacobian_z0, density_ratio_z0] at h0
  norm_num at h0

end D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation
