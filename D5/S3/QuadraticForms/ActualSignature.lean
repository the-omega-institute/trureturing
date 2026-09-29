/- GID: D5/S3/QuadraticForms/ActualSignature
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/ActualSignature
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Polynomial pivots characterize the actual signature of every finite real symmetric matrix. -/

import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

/-!
Polynomial one-coordinate and two-coordinate pivots reduce an arbitrary real
symmetric matrix while preserving its positive-minus-negative inertia count.
The two-coordinate branch handles nonzero matrices whose diagonal vanishes.
The equivalence includes dimension zero and singular matrices.
-/

open scoped BigOperators
open QuadraticForm QuadraticMap
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.QuadraticForms.ActualSignature

abbrev Mat (R : Type*) (n : ℕ) := Matrix (Fin n) (Fin n) R

def residualOne {R : Type*} [CommRing R] {n : ℕ} (A : Mat R (n+1))
    (i : Fin (n+1)) : Mat R n := fun r s =>
  A i i ^ 2 * A (i.succAbove r) (i.succAbove s) -
    A i i * A i (i.succAbove r) * A i (i.succAbove s)
def residualTwo {R : Type*} [CommRing R] {n : ℕ} (A : Mat R (n+2))
    (i : Fin (n+2)) (j : Fin (n+1)) : Mat R n := fun r s =>
  let k := i.succAbove j
  let u := i.succAbove (j.succAbove r)
  let v := i.succAbove (j.succAbove s)
  A i k ^ 2 * A u v - A i k * (A i u * A k v + A k u * A i v)

def Realizes : (n : ℕ) → Mat ℝ n → ℤ → Prop
  | 0, _, z => z = 0
  | n+1, A, z =>
    ((∀ i j, A i j = 0) ∧ z = 0) ∨
    (∃ i, (0 < A i i ∧ Realizes n (residualOne A i) (z-1)) ∨
           (A i i < 0 ∧ Realizes n (residualOne A i) (z+1))) ∨
    (match n with
     | 0 => False
     | m+1 => (∀ i, A i i = 0) ∧ ∃ i j,
         A i (i.succAbove j) ≠ 0 ∧ Realizes m (residualTwo A i j) z)

abbrev signature {V : Type*} [AddCommGroup V] [Module ℝ V] (Q : QuadraticForm ℝ V) : ℤ :=
  (sigPos Q : ℤ) - (sigNeg Q : ℤ)

/-- The recursive polynomial pivot relation is exactly the actual matrix signature. -/
theorem realizes_iff_signature (n : ℕ) (A : Mat ℝ n)
    (hs : ∀ r s, A r s = A s r) (z : ℤ) :
    Realizes n A z ↔ signature A.toQuadraticForm' = z := by
  classical
  have reusePivotOne := (fun {V : Type} [AddCommGroup V] [Module ℝ V]
      (a : ℝ) (ha : a ≠ 0) (l : V →ₗ[ℝ] ℝ) (D : QuadraticForm ℝ V) =>
    (show     let f : (ℝ × V) →ₗ[ℝ] ℝ := LinearMap.fst ℝ ℝ V
      let g : (ℝ × V) →ₗ[ℝ] ℝ := l.comp (LinearMap.snd ℝ ℝ V)
      let Q := a • QuadraticMap.linMulLin f f +
        2 • QuadraticMap.linMulLin f g + D.comp (LinearMap.snd ℝ ℝ V)
      QuadraticMap.Equivalent Q
        ((a • QuadraticMap.linMulLin (LinearMap.id : ℝ →ₗ[ℝ] ℝ) LinearMap.id).prod
          (a^2 • D - a • QuadraticMap.linMulLin l l)) from by
      classical
      dsimp only
      let e : (ℝ × V) ≃ₗ[ℝ] (ℝ × V) :=
        { toFun := fun z => (z.1 - l z.2, a • z.2)
          invFun := fun z => (z.1 + a⁻¹ * l z.2, a⁻¹ • z.2)
          left_inv := by intro z; simp [smul_smul, ha]
          right_inv := by intro z; simp [smul_smul, ha]
          map_add' := by intro x y; ext <;> simp <;> ring
          map_smul' := by intro c x; ext <;> simp [smul_smul] <;> ring }
      apply QuadraticMap.Equivalent.symm
      refine ⟨{ e with map_app' := ?_ }⟩
      intro z
      simp only [QuadraticMap.add_apply, QuadraticMap.smul_apply,
        QuadraticMap.linMulLin_apply, QuadraticMap.comp_apply,
        LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.comp_apply,
        QuadraticMap.prod_apply, QuadraticMap.sub_apply, LinearMap.id_apply,
        e, LinearEquiv.coe_mk, map_smul, QuadraticMap.map_smul, smul_eq_mul]
      ring))

  have reusePivotTwo := (fun {V : Type} [AddCommGroup V] [Module ℝ V]
      (b : ℝ) (hb : b ≠ 0) (u v : V →ₗ[ℝ] ℝ) (D : QuadraticForm ℝ V) =>
    (show     let f : ((ℝ × ℝ) × V) →ₗ[ℝ] ℝ :=
        (LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) V)
      let g : ((ℝ × ℝ) × V) →ₗ[ℝ] ℝ :=
        (LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) V)
      let U := u.comp (LinearMap.snd ℝ (ℝ × ℝ) V)
      let W := v.comp (LinearMap.snd ℝ (ℝ × ℝ) V)
      let Q := (2*b) • QuadraticMap.linMulLin f g +
        2 • QuadraticMap.linMulLin f U + 2 • QuadraticMap.linMulLin g W +
        D.comp (LinearMap.snd ℝ (ℝ × ℝ) V)
      QuadraticMap.Equivalent Q
        (((2*b) • QuadraticMap.linMulLin
          (LinearMap.fst ℝ ℝ ℝ) (LinearMap.snd ℝ ℝ ℝ)).prod
          (b^2 • D - (2*b) • QuadraticMap.linMulLin u v)) from by
      classical
      dsimp only
      let e : ((ℝ × ℝ) × V) ≃ₗ[ℝ] ((ℝ × ℝ) × V) :=
        { toFun := fun z => ((z.1.1 - v z.2, z.1.2 - u z.2), b • z.2)
          invFun := fun z => ((z.1.1 + b⁻¹ * v z.2, z.1.2 + b⁻¹ * u z.2), b⁻¹ • z.2)
          left_inv := by intro z; simp [smul_smul, hb]
          right_inv := by intro z; simp [smul_smul, hb]
          map_add' := by intro x y; ext <;> simp <;> ring
          map_smul' := by intro c x; ext <;> simp [smul_smul] <;> ring }
      apply QuadraticMap.Equivalent.symm
      refine ⟨{ e with map_app' := ?_ }⟩
      intro z
      simp only [QuadraticMap.add_apply, QuadraticMap.smul_apply,
        QuadraticMap.linMulLin_apply, QuadraticMap.comp_apply,
        LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.comp_apply,
        QuadraticMap.prod_apply, QuadraticMap.sub_apply, LinearMap.id_apply,
        e, LinearEquiv.coe_mk, map_smul, QuadraticMap.map_smul, smul_eq_mul]
      ring))

  let splitAt {n : ℕ} (i : Fin (n+1)) : (Fin (n+1) → ℝ) ≃ₗ[ℝ] (ℝ × (Fin n → ℝ)) := {
    toFun x := (x i, fun j => x (i.succAbove j))
    invFun y := i.insertNth y.1 y.2
    left_inv x := Fin.insertNth_self_removeNth i x
    right_inv x := by ext <;> simp
    map_add' x y := rfl
    map_smul' c x := rfl }

  have matrixSplit := (fun {n : ℕ} (A : Mat ℝ (n+1))
      (hs : ∀ r s, A r s = A s r) (i : Fin (n+1)) =>
    (show
      let l : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ j, A i (i.succAbove j) • LinearMap.proj j
      let D := Matrix.toQuadraticForm' (fun r s : Fin n => A (i.succAbove r) (i.succAbove s))
      let f := LinearMap.fst ℝ ℝ (Fin n → ℝ)
      let g := l.comp (LinearMap.snd ℝ ℝ (Fin n → ℝ))
      QuadraticMap.Equivalent A.toQuadraticForm'
        (A i i • QuadraticMap.linMulLin f f +
        2 • QuadraticMap.linMulLin f g + D.comp (LinearMap.snd ℝ ℝ (Fin n → ℝ))) from by
      dsimp only
      refine ⟨{ splitAt i with map_app' := ?_ }⟩
      intro x
      simp only [QuadraticMap.add_apply, QuadraticMap.smul_apply, QuadraticMap.linMulLin_apply,
        QuadraticMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.comp_apply,
        LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul,
        splitAt, LinearEquiv.coe_mk, Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
        Matrix.toLinearMap₂'_apply]
      rw [Fin.sum_univ_succAbove _ i]
      simp_rw [Fin.sum_univ_succAbove _ i]
      rw [Finset.sum_add_distrib]
      have h1 : (∑ j, x i * (x (i.succAbove j) * A i (i.succAbove j))) =
          x i * ∑ j, A i (i.succAbove j) * x (i.succAbove j) := by
        rw [Finset.mul_sum]; congr 1; funext j; ring
      have h2 : (∑ j, x (i.succAbove j) * (x i * A (i.succAbove j) i)) =
          x i * ∑ j, A i (i.succAbove j) * x (i.succAbove j) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl
        intro j _; rw [hs (i.succAbove j) i]; ring
      rw [h1,h2]
      simp only [two_smul]
      ring))

  have matrixOne := (fun {n : ℕ} (A : Mat ℝ (n+1))
      (hs : ∀ r s, A r s = A s r) (i : Fin (n+1)) (hi : A i i ≠ 0) =>
    (show QuadraticMap.Equivalent A.toQuadraticForm'
      ((A i i • QuadraticMap.linMulLin (LinearMap.id : ℝ →ₗ[ℝ] ℝ) LinearMap.id).prod
        (residualOne A i).toQuadraticForm') from by
      let l : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ j, A i (i.succAbove j) • LinearMap.proj j
      let D := Matrix.toQuadraticForm' (fun r s : Fin n => A (i.succAbove r) (i.succAbove s))
      have hsplit := matrixSplit A hs i
      have hpivot := reusePivotOne (A i i) hi l D
      have h := hsplit.trans hpivot
      have hr : (A i i)^2 • D - A i i • QuadraticMap.linMulLin l l =
          (residualOne A i).toQuadraticForm' := by
        ext x
        simp only [QuadraticMap.sub_apply, QuadraticMap.smul_apply, QuadraticMap.linMulLin_apply,
          LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul,
          l,D, Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
          Matrix.toLinearMap₂'_apply, residualOne]
        simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
        congr 1 <;> apply Finset.sum_congr rfl <;> intro r _ <;>
          apply Finset.sum_congr rfl <;> intro s _ <;> ring
      rwa [hr] at h))

  let splitTwo {n : ℕ} (i : Fin (n+2)) (j : Fin (n+1)) :
      (Fin (n+2) → ℝ) ≃ₗ[ℝ] ((ℝ × ℝ) × (Fin n → ℝ)) := {
    toFun x := ((x i,x (i.succAbove j)), fun r => x (i.succAbove (j.succAbove r)))
    invFun y := i.insertNth y.1.1 (j.insertNth y.1.2 y.2)
    left_inv x := by
      funext a
      refine Fin.succAboveCases i ?_ (fun r => ?_) a
      · simp
      · refine Fin.succAboveCases j ?_ (fun s => ?_) r <;> simp
    right_inv x := by ext <;> simp
    map_add' x y := rfl
    map_smul' c x := rfl }

  have matrixTwo := (fun {n : ℕ} (A : Mat ℝ (n+2))
      (hs : ∀ r s, A r s = A s r) (i : Fin (n+2)) (j : Fin (n+1))
      (hdi : A i i = 0) (hdj : A (i.succAbove j) (i.succAbove j) = 0)
      (hb : A i (i.succAbove j) ≠ 0) =>
    (show QuadraticMap.Equivalent A.toQuadraticForm'
      (((2*A i (i.succAbove j)) • QuadraticMap.linMulLin
        (LinearMap.fst ℝ ℝ ℝ) (LinearMap.snd ℝ ℝ ℝ)).prod
        (residualTwo A i j).toQuadraticForm') from by
      let k := i.succAbove j
      let t : Fin n → Fin (n+2) := fun r => i.succAbove (j.succAbove r)
      let u : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ r, A i (t r) • LinearMap.proj r
      let v : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ r, A k (t r) • LinearMap.proj r
      let D := Matrix.toQuadraticForm' (fun r s : Fin n => A (t r) (t s))
      let f := (LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) (Fin n → ℝ))
      let g := (LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) (Fin n → ℝ))
      let U := u.comp (LinearMap.snd ℝ (ℝ × ℝ) (Fin n → ℝ))
      let W := v.comp (LinearMap.snd ℝ (ℝ × ℝ) (Fin n → ℝ))
      have he : QuadraticMap.Equivalent A.toQuadraticForm'
          ((2*A i k) • QuadraticMap.linMulLin f g + 2 • QuadraticMap.linMulLin f U +
            2 • QuadraticMap.linMulLin g W + D.comp (LinearMap.snd ℝ (ℝ × ℝ) (Fin n → ℝ))) := by
        refine ⟨{ splitTwo i j with map_app' := ?_ }⟩
        intro x
        simp only [f,g,U,W,u,v,D, QuadraticMap.add_apply, QuadraticMap.smul_apply,
          QuadraticMap.linMulLin_apply, QuadraticMap.comp_apply, LinearMap.fst_apply,
          LinearMap.snd_apply, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
          LinearMap.proj_apply, smul_eq_mul, splitTwo, LinearEquiv.coe_mk,
          Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply]
        rw [Fin.sum_univ_succAbove _ i]
        simp_rw [Fin.sum_univ_succAbove _ i]
        simp_rw [Fin.sum_univ_succAbove _ j]
        simp only [Finset.sum_add_distrib, hdi, hdj, mul_zero, zero_mul, zero_add, add_zero]
        have hki : A (i.succAbove j) i = A i (i.succAbove j) := hs _ _
        have hci : ∀ r, A (t r) i = A i (t r) := fun r => hs _ _
        have hck : ∀ r, A (t r) k = A k (t r) := fun r => hs _ _
        simp only [t,k] at hci hck ⊢
        simp only [hki,hci,hck,two_smul]
        simp only [Finset.mul_sum,Finset.sum_mul]
        simp only [mul_assoc, mul_left_comm, mul_comm]
        simp only [← Finset.sum_mul, ← Finset.mul_sum]
        ring
      have hp := reusePivotTwo (A i k) hb u v D
      have hr : (A i k)^2 • D - (2*A i k) • QuadraticMap.linMulLin u v =
          (residualTwo A i j).toQuadraticForm' := by
        ext x
        simp only [QuadraticMap.sub_apply, QuadraticMap.smul_apply, QuadraticMap.linMulLin_apply,
          u,v,D,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.proj_apply,smul_eq_mul,
          Matrix.toQuadraticForm',LinearMap.BilinMap.toQuadraticMap_apply,Matrix.toLinearMap₂'_apply,
          residualTwo]
        change _ = ∑ r, ∑ s, x r * (x s * ((A i k)^2 * A (t r) (t s) - A i k * (A i (t r) * A k (t s) + A k (t r) * A i (t s))))
        simp only [mul_sub,sub_mul,mul_add,add_mul,Finset.sum_sub_distrib,Finset.sum_add_distrib,
          Finset.mul_sum,Finset.sum_mul]
        have hswap : (∑ r, ∑ s, x r * (x s * (A i k * (A k (t r) * A i (t s))))) =
            ∑ r, ∑ s, x r * (x s * (A i k * (A i (t r) * A k (t s)))) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro r _; apply Finset.sum_congr rfl; intro s _; ring
        rw [← hswap]
        simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro r _; apply Finset.sum_congr rfl; intro s _; ring
      have h := he.trans hp
      rwa [hr] at h))

  have signatureProd := (fun {V W : Type} [AddCommGroup V] [AddCommGroup W]
      [Module ℝ V] [Module ℝ W] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
      (Q : QuadraticForm ℝ V) (R : QuadraticForm ℝ W) =>
    (show signature (Q.prod R) = signature Q + signature R from by
      classical
      obtain ⟨v,hv⟩ := Q.equivalent_weightedSumSquares
      obtain ⟨w,hw⟩ := R.equivalent_weightedSumSquares
      let e := LinearEquiv.sumArrowLequivProdArrow (Fin (Module.finrank ℝ V))
        (Fin (Module.finrank ℝ W)) ℝ ℝ
      have he : QuadraticMap.Equivalent (weightedSumSquares ℝ (Sum.elim v w))
          ((weightedSumSquares ℝ v).prod (weightedSumSquares ℝ w)) := by
        refine ⟨{ e with map_app' := ?_ }⟩
        intro x
        simp [e, QuadraticMap.prod_apply, weightedSumSquares_apply, Fintype.sum_sum_type,
          LinearEquiv.sumArrowLequivProdArrow]
      have h := (hv.prod hw).trans he.symm
      have hc (p : Fin (Module.finrank ℝ V) ⊕ Fin (Module.finrank ℝ W) → Prop) :
          {i | p i}.ncard = {i | p (.inl i)}.ncard + {i | p (.inr i)}.ncard := by
        change Nat.card {i // p i} = Nat.card {i // p (.inl i)} + Nat.card {i // p (.inr i)}
        rw [Nat.card_congr (Equiv.subtypeSum (p := p)), Nat.card_sum]
      simp only [signature, h.sigPos_eq, h.sigNeg_eq, hv.sigPos_eq, hv.sigNeg_eq,
        hw.sigPos_eq, hw.sigNeg_eq, sigPos_weightedSumSquares, sigNeg_weightedSumSquares]
      rw [hc, hc]
      simp only [Sum.elim_inl, Sum.elim_inr, Nat.cast_add]
      ring))

  have signatureScalar := (fun (a : ℝ) =>
    (show signature (a • QuadraticMap.linMulLin (LinearMap.id : ℝ →ₗ[ℝ] ℝ) LinearMap.id) =
        (if 0 < a then (1 : ℤ) else if a < 0 then -1 else 0) from by
      classical
      let Q := a • QuadraticMap.linMulLin (LinearMap.id : ℝ →ₗ[ℝ] ℝ) LinearMap.id
      have he : QuadraticMap.Equivalent (weightedSumSquares ℝ (fun _ : Fin 1 => a)) Q := by
        refine ⟨{ LinearEquiv.funUnique (Fin 1) ℝ ℝ with map_app' := ?_ }⟩
        intro x
        simp [Q, weightedSumSquares_apply, LinearEquiv.funUnique_apply]
      change signature Q = _
      simp only [signature, ← he.sigPos_eq, ← he.sigNeg_eq,
        sigPos_weightedSumSquares, sigNeg_weightedSumSquares]
      by_cases hp : 0 < a
      · have hn : ¬ a < 0 := by linarith
        simp [hp,hn]
      · by_cases hn : a < 0 <;> simp [hp,hn]))

  have signatureHyperbolic := (fun (b : ℝ) =>
    (show signature ((2*b) • QuadraticMap.linMulLin
        (LinearMap.fst ℝ ℝ ℝ) (LinearMap.snd ℝ ℝ ℝ)) = 0 from by
      let Q := (2*b) • QuadraticMap.linMulLin (LinearMap.fst ℝ ℝ ℝ) (LinearMap.snd ℝ ℝ ℝ)
      have he : QuadraticMap.Equivalent Q (-Q) := by
        refine ⟨{ LinearEquiv.prodCongr (LinearEquiv.neg ℝ) (LinearEquiv.refl ℝ ℝ) with map_app' := ?_ }⟩
        intro x
        simp [Q]
      change (sigPos Q : ℤ) - (sigNeg Q : ℤ) = 0
      rw [he.sigPos_eq, sigPos_neg, sub_self]))
  classical
  have hz (m : ℕ) (B : Mat ℝ m) (hB : ∀ i j, B i j = 0) :
      signature B.toQuadraticForm' = 0 := by
    have hq : B.toQuadraticForm' = (0 : QuadraticForm ℝ (Fin m → ℝ)) := by
      ext x
      simp [Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply, hB]
    have hn : -(0 : QuadraticForm ℝ (Fin m → ℝ)) = 0 := neg_zero
    rw [hq]
    change (sigPos (0 : QuadraticForm ℝ (Fin m → ℝ)) : ℤ) -
      (sigPos (-(0 : QuadraticForm ℝ (Fin m → ℝ))) : ℤ) = 0
    rw [hn, sub_self]
  have hs1 {m : ℕ} (B : Mat ℝ (m+1)) (hB : ∀ r s, B r s = B s r) (i) :
      ∀ r s, residualOne B i r s = residualOne B i s r := by
    intro r s
    simp only [residualOne]
    rw [hB (i.succAbove r) (i.succAbove s)]
    ring
  have hs2 {m : ℕ} (B : Mat ℝ (m+2)) (hB : ∀ r s, B r s = B s r) (i j) :
      ∀ r s, residualTwo B i j r s = residualTwo B i j s r := by
    intro r s
    simp only [residualTwo]
    rw [hB (i.succAbove (j.succAbove r)) (i.succAbove (j.succAbove s))]
    ring
  have h1 {m : ℕ} (B : Mat ℝ (m+1)) (hB : ∀ r s, B r s = B s r)
      (i) (hi : B i i ≠ 0) :
      signature B.toQuadraticForm' =
        (if 0 < B i i then 1 else if B i i < 0 then -1 else 0) +
          signature (residualOne B i).toQuadraticForm' := by
    have he := matrixOne B hB i hi
    have hp := signatureProd
      (B i i • QuadraticMap.linMulLin (LinearMap.id : ℝ →ₗ[ℝ] ℝ) LinearMap.id)
      (residualOne B i).toQuadraticForm'
    have hc := signatureScalar (B i i)
    calc
      _ = signature ((B i i • QuadraticMap.linMulLin
          (LinearMap.id : ℝ →ₗ[ℝ] ℝ) LinearMap.id).prod
            (residualOne B i).toQuadraticForm') := by
        simp only [signature, he.sigPos_eq, he.sigNeg_eq]
      _ = _ := by rw [hp, hc]
  have h2 {m : ℕ} (B : Mat ℝ (m+2)) (hB : ∀ r s, B r s = B s r)
      (i j) (hd : ∀ i, B i i = 0) (hi : B i (i.succAbove j) ≠ 0) :
      signature B.toQuadraticForm' = signature (residualTwo B i j).toQuadraticForm' := by
    have he := matrixTwo B hB i j (hd i) (hd _) hi
    have hp := signatureProd
      ((2*B i (i.succAbove j)) • QuadraticMap.linMulLin
        (LinearMap.fst ℝ ℝ ℝ) (LinearMap.snd ℝ ℝ ℝ))
      (residualTwo B i j).toQuadraticForm'
    have hc := signatureHyperbolic (B i (i.succAbove j))
    calc
      _ = signature (((2*B i (i.succAbove j)) • QuadraticMap.linMulLin
          (LinearMap.fst ℝ ℝ ℝ) (LinearMap.snd ℝ ℝ ℝ)).prod
            (residualTwo B i j).toQuadraticForm') := by
        simp only [signature, he.sigPos_eq, he.sigNeg_eq]
      _ = _ := by rw [hp, hc, zero_add]
  induction n using Nat.strong_induction_on generalizing z with
  | h n ih =>
    cases n with
    | zero =>
      have h := hz 0 A (fun i => Fin.elim0 i)
      simp [Realizes, h, eq_comm]
    | succ m =>
      rw [Realizes.eq_def]
      dsimp only
      constructor
      · rintro (⟨hA,rfl⟩ | ⟨i,hi⟩ | htwo)
        · exact hz _ A hA
        · rcases hi with ⟨hi,hr⟩ | ⟨hi,hr⟩
          · have hr' := (ih m (by omega) (residualOne A i) (hs1 A hs i) (z-1)).mp hr
            have he := h1 A hs i (ne_of_gt hi)
            simp only [if_pos hi] at he
            omega
          · have hr' := (ih m (by omega) (residualOne A i) (hs1 A hs i) (z+1)).mp hr
            have he := h1 A hs i (ne_of_lt hi)
            have hn : ¬ 0 < A i i := by linarith
            simp only [if_neg hn, if_pos hi] at he
            omega
        · cases m with
          | zero => exact htwo.elim
          | succ l =>
            obtain ⟨hd,i,j,hij,hr⟩ := htwo
            have hr' := (ih l (by omega) (residualTwo A i j) (hs2 A hs i j) z).mp hr
            exact (h2 A hs i j hd hij).trans hr'
      · intro he
        by_cases ha : ∀ i j, A i j = 0
        · exact Or.inl ⟨ha, he.symm.trans (hz _ A ha)⟩
        by_cases hd : ∀ i, A i i = 0
        · cases m with
          | zero =>
            exfalso
            apply ha
            intro i j
            have hij : j = i := by apply Fin.ext; omega
            simpa [hij] using hd i
          | succ l =>
            push_neg at ha
            obtain ⟨i,k,hik⟩ := ha
            have hki : k ≠ i := by intro h; subst k; exact hik (hd i)
            obtain ⟨j,hj⟩ := Fin.exists_succAbove_eq hki
            subst k
            refine Or.inr (Or.inr ⟨hd,i,j,hik,?_⟩)
            apply (ih l (by omega) (residualTwo A i j) (hs2 A hs i j) z).mpr
            exact (h2 A hs i j hd hik).symm.trans he
        · push_neg at hd
          obtain ⟨i,hi⟩ := hd
          refine Or.inr (Or.inl ⟨i,?_⟩)
          rcases lt_or_gt_of_ne hi with hn | hp
          · refine Or.inr ⟨hn, ?_⟩
            apply (ih m (by omega) (residualOne A i) (hs1 A hs i) (z+1)).mpr
            have hh := h1 A hs i hi
            have hnp : ¬ 0 < A i i := by linarith
            simp only [if_neg hnp, if_pos hn] at hh
            omega
          · refine Or.inl ⟨hp, ?_⟩
            apply (ih m (by omega) (residualOne A i) (hs1 A hs i) (z-1)).mpr
            have hh := h1 A hs i hi
            simp only [if_pos hp] at hh
            omega

end D5.S3.QuadraticForms.ActualSignature
