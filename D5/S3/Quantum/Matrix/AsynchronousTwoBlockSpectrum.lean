/- GID: D5/S3/Quantum/Matrix/AsynchronousTwoBlockSpectrum
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/AsynchronousTwoBlockSpectrum
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Nonzero spectral values of the actual two-block delay matrix are roots of the rectangular product spectrum. -/

import D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Data.Matrix.Block

/-! Exact nonzero spectra for the literal constant-delay history operator. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Matrix
open D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs (Vtx)
open D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation
open scoped BigOperators

namespace D5.S3.Quantum.Matrix.AsynchronousTwoBlockSpectrum

/-- Sum coordinates and the two dependent block coordinates describe the same vector space. -/
def blockEquiv (m n : ℕ) : (Fin m ⊕ Fin n) ≃ Vtx (![m,n] : Fin 2 → ℕ) where
  toFun p := match p with
    | .inl i => ⟨0, i⟩
    | .inr j => ⟨1, j⟩
  invFun p := Fin.cases (fun x => Sum.inl x)
    (fun i => Fin.cases (fun x => Sum.inr x) (fun j => Fin.elim0 j) i) p.1 p.2
  left_inv := by intro p; cases p <;> rfl
  right_inv := by rintro ⟨i, x⟩; fin_cases i <;> rfl

@[simp] private theorem blockEquiv_symm_left (m n : ℕ) (i : Fin m) :
    (blockEquiv m n).symm ⟨0,i⟩ = Sum.inl i := rfl

@[simp] private theorem blockEquiv_symm_right (m n : ℕ) (j : Fin n) :
    (blockEquiv m n).symm ⟨1,j⟩ = Sum.inr j := rfl

/-- The zero-diagonal rectangular block matrix in the coordinates of the history operator. -/
def zeroDiagonal {m n : ℕ} (U : Matrix (Fin m) (Fin n) ℝ)
    (V : Matrix (Fin n) (Fin m) ℝ) :
    Matrix (Vtx (![m,n] : Fin 2 → ℕ)) (Vtx (![m,n] : Fin 2 → ℕ)) ℝ :=
  Matrix.reindexAlgEquiv ℝ ℝ (blockEquiv m n)
    (Matrix.fromBlocks 0 U V 0)

private theorem shift_row {ℓ : ℕ} {sizes : Fin ℓ → ℕ}
    (M : Matrix (Vtx sizes) (Vtx sizes) ℝ) (δ : Fin ℓ → Fin ℓ → ℕ)
    (K : ℕ) (H : Fin (K+1) × Vtx sizes → ℂ)
    (r : Fin (K+1)) (p : Vtx sizes) (hr : r.val ≠ 0) :
    ((asyncMatrix M δ K).map (algebraMap ℝ ℂ) *ᵥ H) (r,p) =
      H (⟨r.val-1, by omega⟩,p) := by
  classical
  let pred : Fin (K+1) := ⟨r.val-1, by omega⟩
  change (∑ s, ((asyncMatrix M δ K).map (algebraMap ℝ ℂ)) (r,p) s * H s) = H (pred,p)
  rw [Fintype.sum_eq_single (pred,p)]
  · simp [asyncMatrix, Matrix.map_apply, hr, pred, show r.val-1+1=r.val by omega]
  · rintro ⟨s,q⟩ hne
    have hns : ¬ (s.val+1=r.val ∧ q=p) := by
      rintro ⟨hs, rfl⟩
      apply hne
      congr 1
      apply Fin.ext
      dsimp [pred]
      omega
    simp [asyncMatrix, Matrix.map_apply, hr, hns]

private theorem left_row {m n a b K : ℕ}
    (U : Matrix (Fin m) (Fin n) ℝ) (V : Matrix (Fin n) (Fin m) ℝ)
    (haK : a ≤ K) (H : Fin (K+1) × Vtx (![m,n] : Fin 2 → ℕ) → ℂ)
    (i : Fin m) :
    ((asyncMatrix (zeroDiagonal U V) !![0,b; a,0] K).map (algebraMap ℝ ℂ) *ᵥ H)
        (0,⟨0,i⟩) =
      ∑ j : Fin n, (U i j : ℂ) * H (⟨a,by omega⟩,⟨1,j⟩) := by
  classical
  let da : Fin (K+1) := ⟨a,by omega⟩
  have slot (s : Fin (K+1)) : (s.val=a) ↔ s=da := by
    constructor
    · intro h; apply Fin.ext; exact h
    · intro h; subst s; rfl
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fintype.sum_sigma,
    Fin.sum_univ_two]
  simp [asyncMatrix, zeroDiagonal, Matrix.reindex_apply, Matrix.map_apply,
    slot, da]
  rw [Fintype.sum_eq_single da]
  · simp [da]
  · intro s hs
    simp [show s ≠ ⟨a,by omega⟩ from hs]

private theorem right_row {m n a b K : ℕ}
    (U : Matrix (Fin m) (Fin n) ℝ) (V : Matrix (Fin n) (Fin m) ℝ)
    (hbK : b ≤ K) (H : Fin (K+1) × Vtx (![m,n] : Fin 2 → ℕ) → ℂ)
    (j : Fin n) :
    ((asyncMatrix (zeroDiagonal U V) !![0,b; a,0] K).map (algebraMap ℝ ℂ) *ᵥ H)
        (0,⟨1,j⟩) =
      ∑ i : Fin m, (V j i : ℂ) * H (⟨b,by omega⟩,⟨0,i⟩) := by
  classical
  let db : Fin (K+1) := ⟨b,by omega⟩
  have slot (s : Fin (K+1)) : (s.val=b) ↔ s=db := by
    constructor
    · intro h; apply Fin.ext; exact h
    · intro h; subst s; rfl
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fintype.sum_sigma,
    Fin.sum_univ_two]
  simp [asyncMatrix, zeroDiagonal, Matrix.reindex_apply, Matrix.map_apply,
    slot, db]
  rw [Fintype.sum_eq_single db]
  · simp [db]
  · intro s hs
    simp [show s ≠ ⟨b,by omega⟩ from hs]

private theorem history_formula {ℓ : ℕ} {sizes : Fin ℓ → ℕ}
    (M : Matrix (Vtx sizes) (Vtx sizes) ℝ) (δ : Fin ℓ → Fin ℓ → ℕ)
    (K : ℕ) (H : Fin (K+1) × Vtx sizes → ℂ) (z : ℂ) (hz : z ≠ 0)
    (he : (asyncMatrix M δ K).map (algebraMap ℝ ℂ) *ᵥ H = z • H) :
    ∀ (s : ℕ) (hs : s<K+1) (p : Vtx sizes), H (⟨s,hs⟩,p) = z⁻¹^s * H (0,p) := by
  intro s
  induction s with
  | zero => intro hs p; simp
  | succ s ih =>
    intro hs p
    have hstep := congrFun he (⟨s+1,hs⟩,p)
    rw [shift_row M δ K H _ p (by simp)] at hstep
    change H (⟨s+1-1,_⟩,p) = z * H (⟨s+1,hs⟩,p) at hstep
    have hp : (⟨s+1-1,by omega⟩ : Fin (K+1)) = ⟨s,by omega⟩ := by
      apply Fin.ext; simp
    rw [hp] at hstep
    calc H (⟨s+1,hs⟩,p) = z⁻¹ * (z * H (⟨s+1,hs⟩,p)) := by simp [←mul_assoc,hz]
      _ = z⁻¹ * H (⟨s,by omega⟩,p) := by rw [←hstep]
      _ = z⁻¹ ^ (s+1) * H (0,p) := by rw [ih (by omega) p, pow_succ]; ring


/-- Every nonzero delayed spectral value is exactly an Lth root of a product spectral value. -/
theorem nonzero_spectrum_iff {m n a b K : ℕ}
    (U : Matrix (Fin m) (Fin n) ℝ) (V : Matrix (Fin n) (Fin m) ℝ)
    (haK : a ≤ K) (hbK : b ≤ K) (z : ℂ) (hz : z ≠ 0) :
    z ∈ spectrum ℂ ((asyncMatrix (zeroDiagonal U V) !![0,b; a,0] K).map
        (algebraMap ℝ ℂ)) ↔
      z ^ (a+b+2) ∈ spectrum ℂ ((U*V).map (algebraMap ℝ ℂ)) := by
  classical
  let A := U.map (algebraMap ℝ ℂ)
  let D := V.map (algebraMap ℝ ℂ)
  let CB := (asyncMatrix (zeroDiagonal U V) !![0,b; a,0] K).map (algebraMap ℝ ℂ)
  have cancel (t : ℕ) : z^t * z⁻¹^t = 1 := by rw [←mul_pow]; simp [hz]
  constructor
  · intro hspec
    have hlin : z ∈ spectrum ℂ CB.toLin' := by rwa [Matrix.spectrum_toLin']
    obtain ⟨H,hH⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hlin).exists_hasEigenvector
    have he : CB *ᵥ H = z • H := by simpa only [Matrix.toLin'_apply] using hH.apply_eq_smul
    let u : Fin m → ℂ := fun i => H (0,⟨0,i⟩)
    let v : Fin n → ℂ := fun j => H (0,⟨1,j⟩)
    have hist := history_formula (zeroDiagonal U V) !![0,b; a,0] K H z hz he
    have hu : A *ᵥ v = z^(a+1) • u := by
      funext i
      have hrow := congrFun he (0,⟨0,i⟩)
      rw [left_row U V haK] at hrow
      simp_rw [hist a (by omega)] at hrow
      have hr : z⁻¹^a * (A *ᵥ v) i = z * u i := by
        simpa [A,u,v,Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc,mul_left_comm] using hrow
      change (A *ᵥ v) i = z^(a+1) * u i
      calc (A *ᵥ v) i = z^a * (z⁻¹^a * (A *ᵥ v) i) := by rw [←mul_assoc,cancel]; simp
        _ = z^a * (z * u i) := by rw [hr]
        _ = z^(a+1) * u i := by rw [pow_succ]; ring
    have hv : D *ᵥ u = z^(b+1) • v := by
      funext j
      have hrow := congrFun he (0,⟨1,j⟩)
      rw [right_row U V hbK] at hrow
      simp_rw [hist b (by omega)] at hrow
      have hr : z⁻¹^b * (D *ᵥ u) j = z * v j := by
        simpa [D,u,v,Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc,mul_left_comm] using hrow
      change (D *ᵥ u) j = z^(b+1) * v j
      calc (D *ᵥ u) j = z^b * (z⁻¹^b * (D *ᵥ u) j) := by rw [←mul_assoc,cancel]; simp
        _ = z^b * (z * v j) := by rw [hr]
        _ = z^(b+1) * v j := by rw [pow_succ]; ring
    have hune : u ≠ 0 := by
      intro huz
      have hvz : v = 0 := by
        have h : z^(b+1) • v = 0 := by rw [←hv,huz,Matrix.mulVec_zero]
        exact (smul_eq_zero.mp h).resolve_left (pow_ne_zero _ hz)
      apply hH.2
      funext rp
      rcases rp with ⟨r,⟨i,x⟩⟩
      rw [hist r.val r.isLt]
      fin_cases i
      · change z⁻¹^r.val * u x = 0
        rw [huz]
        change z⁻¹^r.val * (0 : ℂ) = 0
        exact mul_zero _
      · change z⁻¹^r.val * v x = 0
        rw [hvz]
        change z⁻¹^r.val * (0 : ℂ) = 0
        exact mul_zero _
    apply D5.S3.Combinatorics.NonBacktracking.LaplacianGapMinDegree.eigenpair_mem_spectrum
      _ (z^(a+b+2)) u hune
    rw [Matrix.map_mul]
    change (A*D) *ᵥ u = z^(a+b+2) • u
    rw [←Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, hu, smul_smul, ←pow_add]
    congr 1
    congr 1
    omega
  · intro hspec
    have hlin : z^(a+b+2) ∈ spectrum ℂ ((U*V).map (algebraMap ℝ ℂ)).toLin' := by
      rwa [Matrix.spectrum_toLin']
    obtain ⟨u,hu⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hlin).exists_hasEigenvector
    have hPu : (A*D) *ᵥ u = z^(a+b+2) • u := by
      simpa only [Matrix.toLin'_apply,Matrix.map_mul] using hu.apply_eq_smul
    let v : Fin n → ℂ := z⁻¹^(b+1) • (D *ᵥ u)
    let base : Vtx (![m,n] : Fin 2 → ℕ) → ℂ :=
      fun p => Sum.elim u v ((blockEquiv m n).symm p)
    let H : Fin (K+1) × Vtx (![m,n] : Fin 2 → ℕ) → ℂ :=
      fun rp => z⁻¹^rp.1.val * base rp.2
    have hH : H ≠ 0 := by
      intro hzero
      apply hu.2
      funext i
      have hi := congrFun hzero (0,⟨0,i⟩)
      simpa [H,base] using hi
    have hc : z⁻¹^(a+b+1) * z^(a+b+2) = z := by
      rw [show a+b+2=(a+b+1)+1 by omega,pow_succ z,←mul_assoc,←mul_pow]
      simp [hz]
    apply D5.S3.Combinatorics.NonBacktracking.LaplacianGapMinDegree.eigenpair_mem_spectrum
      CB z H hH
    funext rp
    rcases rp with ⟨r,p⟩
    by_cases hr : r.val=0
    · have rz : r=0 := Fin.ext hr
      subst r
      rcases p with ⟨i,x⟩
      fin_cases i
      · change ((asyncMatrix (zeroDiagonal U V) !![0,b; a,0] K).map
            (algebraMap ℝ ℂ) *ᵥ H) (0,⟨0,x⟩) = z * H (0,⟨0,x⟩)
        rw [left_row U V haK]
        simp only [H,base,blockEquiv_symm_left,blockEquiv_symm_right,
          Sum.elim_inl,Sum.elim_inr,Fin.val_zero,pow_zero,one_mul]
        change (∑ j, (U x j : ℂ) * (z⁻¹^a * v j)) = z * u x
        calc (∑ j, (U x j : ℂ) * (z⁻¹^a * v j)) = z⁻¹^a * (A *ᵥ v) x := by
              simp [A,Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc,mul_left_comm]
          _ = z⁻¹^a * (z⁻¹^(b+1) * ((A*D) *ᵥ u) x) := by
              rw [show A *ᵥ v = z⁻¹^(b+1) • ((A*D) *ᵥ u) by
                dsimp [v]; rw [Matrix.mulVec_smul,Matrix.mulVec_mulVec]]
              rfl
          _ = z⁻¹^a * (z⁻¹^(b+1) * (z^(a+b+2) * u x)) := by rw [hPu]; rfl
          _ = z * u x := by
              rw [←mul_assoc,←mul_assoc,←pow_add,show a+(b+1)=a+b+1 by omega,hc]
      · change ((asyncMatrix (zeroDiagonal U V) !![0,b; a,0] K).map
            (algebraMap ℝ ℂ) *ᵥ H) (0,⟨1,x⟩) = z * H (0,⟨1,x⟩)
        rw [right_row U V hbK]
        simp only [H,base,blockEquiv_symm_left,blockEquiv_symm_right,
          Sum.elim_inl,Sum.elim_inr,Fin.val_zero,pow_zero,one_mul]
        change (∑ i, (V x i : ℂ) * (z⁻¹^b * u i)) = z * v x
        have hb : z * z⁻¹^(b+1) = z⁻¹^b := by
          rw [pow_succ]
          calc z * (z⁻¹^b * z⁻¹) = (z * z⁻¹) * z⁻¹^b := by ring
            _ = z⁻¹^b := by simp [hz]
        simpa [D,v,Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc,mul_left_comm,hb]
          using congrArg (fun t : ℂ => t * (D *ᵥ u) x) hb.symm
    · rw [shift_row (zeroDiagonal U V) !![0,b; a,0] K H r p hr]
      change z⁻¹^(r.val-1) * base p = z * (z⁻¹^r.val * base p)
      have hs : r.val=(r.val-1)+1 := by omega
      conv_rhs => rw [hs,pow_succ]
      calc z⁻¹^(r.val-1) * base p = (z * z⁻¹) * (z⁻¹^(r.val-1) * base p) := by simp [hz]
        _ = z * (z⁻¹^(r.val-1) * z⁻¹ * base p) := by ring

end D5.S3.Quantum.Matrix.AsynchronousTwoBlockSpectrum
