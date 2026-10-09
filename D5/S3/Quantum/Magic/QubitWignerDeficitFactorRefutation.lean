/- GID: D5/S3/Quantum/Magic/QubitWignerDeficitFactorRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Magic/QubitWignerDeficitFactorRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Magic/QubitWignerDeficitFactorRefutation.claim; result=D5/S3/Quantum/Magic/QubitWignerDeficitFactorRefutation.result; claim=D5/S3/Quantum/Magic/QubitWignerDeficitFactorRefutation.claim
   digest: Two pure equatorial states give incompatible factored deficits at one positive-product state. -/
/-
proof_shape: result: content
escape_witness: dual_certificate and entangled_stabilizer supply the matching joint-distance certificates.
admission_basis: open-problem-resolution (#14651; Refuted)
Direct frozen dependency: D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.
-/
import D5.S3.Quantum.Magic.QubitWignerDistanceTensorRules
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
noncomputable section
namespace D5.S3.Quantum.Magic.QubitWignerDeficitFactorRefutation
open Matrix Complex
open D5.S3.Quantum.FiniteDimensional
open D5.S3.QuantumBounds.CHSHWitness (TwoQubitMatrix)
open D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsDensity)
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence (pauliSet)
open D5.S3.Quantum.Magic.WignerDistanceMinimum
open D5.S3.Quantum.Magic.QubitWignerDistanceTensorRules
open scoped Kronecker ComplexOrder

def deficit (ρ σ : QubitMatrix) : ℝ :=
  (1 + COne ρ) * (1 + COne σ) - 1 - CTwo (ρ ⊗ₖ σ)
def claim : Prop := ∃ f : QubitMatrix → ℝ, ∀ ρ σ : QubitMatrix,
  IsDensity ρ → bloch ρ .Z = 0 → 0 < COne ρ → IsDensity σ →
  0 < bloch σ .X * bloch σ .Y * bloch σ .Z → deficit ρ σ = COne ρ * f σ

private def rhoA : QubitMatrix := !![1/2, 3/10 - 2/5*Complex.I; 3/10 + 2/5*Complex.I, 1/2]
private def rhoB : QubitMatrix := !![1/2, 5/26 - 6/13*Complex.I; 5/26 + 6/13*Complex.I, 1/2]
private def sigma : QubitMatrix := !![17/18, 1/18 - 2/9*Complex.I; 1/18 + 2/9*Complex.I, 1/18]
private def dual (a : PhasePoint × PhasePoint) : ℚ :=
  (!![1,1,-1,1; -1,-1,1,-1; 1,-1,-1,-1; 1,-1,-1,-1] : Matrix (Fin 4) (Fin 4) ℚ)
    (finProdFinEquiv a.1) (finProdFinEquiv a.2)

private theorem dual_certificate : ∀ w ∈ Enumeration.candidates,
    (∑ a : PhasePoint × PhasePoint, dual a * w a) ≤ 1/2 := by
  decide +kernel

private theorem dual_free_bound (v : PhasePoint × PhasePoint → ℝ)
    (hv : v ∈ Wfree phasePointTwo pauliTwo) :
    (∑ a, (dual a : ℝ) * v a) ≤ 1/2 := by
  have vertices (τ : TwoQubitMatrix) (hτ : τ ∈ Stab pauliTwo) :
      (∑ a, (dual a : ℝ) * WignerTwo τ a) ≤ 1/2 := by
    obtain ⟨u,v,e,d,h,rfl⟩ := stabilizer_two_generators τ hτ
    rw [projector_wigner u v e d h]
    change (∑ a, (dual a : ℝ) * (Enumeration.candidate u v e d a : ℝ)) ≤ 1/2
    have hc := (Rat.cast_le (K := ℝ)).mpr (dual_certificate _ (candidate_mem u v e d h))
    simpa only [Rat.cast_sum,Rat.cast_mul,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hc
  apply convexHull_min ?_ ?_ hv
  · rintro _ ⟨τ,hτ,rfl⟩; exact vertices τ hτ
  · intro x hx y hy a b ha hb hab
    change (∑ i, (dual i : ℝ) * (a*x i+b*y i)) ≤ 1/2
    have he : (∑ i, (dual i : ℝ) * (a*x i+b*y i)) =
        a*(∑ i, (dual i : ℝ)*x i)+b*(∑ i, (dual i : ℝ)*y i) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      congr 1; ext i; ring
    change (∑ i, (dual i : ℝ)*x i) ≤ 1/2 at hx
    change (∑ i, (dual i : ℝ)*y i) ≤ 1/2 at hy
    rw [he]; nlinarith

private def entVector (i : Fin 2 × Fin 2) : ℂ :=
  (!![1/2,-1/2; Complex.I/2,Complex.I/2] : QubitMatrix) i.1 i.2
private def entangled : TwoQubitMatrix := Matrix.vecMulVec entVector (star entVector)

private theorem entangled_stabilizer : entangled ∈ Stab pauliTwo := by
  classical
  let mats : Fin 4 → TwoQubitMatrix :=
    ![1,pauliMatrix .X ⊗ₖ pauliMatrix .Y,pauliMatrix .Y ⊗ₖ pauliMatrix .Z,
      -(pauliMatrix .Z ⊗ₖ pauliMatrix .X)]
  have hunit (k : Fin 4) : mats k ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    fin_cases k <;> ext i j <;>
      rcases i with ⟨i,i'⟩ <;> rcases j with ⟨j,j'⟩ <;>
      fin_cases i <;> fin_cases i' <;> fin_cases j <;> fin_cases j' <;>
      norm_num [Matrix.vecMul,dotProduct,Matrix.cons_val_two,Matrix.cons_val_three,
        Matrix.head_cons,Matrix.tail_cons,Complex.star_def,map_div₀,map_ofNat,mats,pauliMatrix,qubitX,qubitZ,Matrix.mul_apply,Fintype.sum_prod_type,
        Fin.sum_univ_two,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,
        Matrix.kroneckerMap_apply,Matrix.ofNat_apply,Complex.ext_iff]
  let U (k : Fin 4) : Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ := ⟨mats k,hunit k⟩
  let table : Fin 4 → Fin 4 → Fin 4 :=
    ![![0,1,2,3],![1,0,3,2],![2,3,0,1],![3,2,1,0]]
  have hmul (k l : Fin 4) : U k * U l = U (table k l) := by
    apply Subtype.ext
    fin_cases k <;> fin_cases l <;> ext i j <;>
      rcases i with ⟨i,i'⟩ <;> rcases j with ⟨j,j'⟩ <;>
      fin_cases i <;> fin_cases i' <;> fin_cases j <;> fin_cases j' <;>
      norm_num [Matrix.vecMul,dotProduct,Matrix.cons_val_two,Matrix.cons_val_three,
        Matrix.head_cons,Matrix.tail_cons,Complex.star_def,map_div₀,map_ofNat,U,mats,table,pauliMatrix,qubitX,qubitZ,Matrix.mul_apply,
        Fintype.sum_prod_type,Fin.sum_univ_two,Matrix.kroneckerMap_apply,
        Matrix.ofNat_apply,Complex.ext_iff]
  have hinv (k : Fin 4) : (U k)⁻¹ = U k := by
    apply Subtype.ext
    fin_cases k <;> ext i j <;>
      rcases i with ⟨i,i'⟩ <;> rcases j with ⟨j,j'⟩ <;>
      fin_cases i <;> fin_cases i' <;> fin_cases j <;> fin_cases j' <;>
      norm_num [Matrix.vecMul,dotProduct,Matrix.cons_val_two,Matrix.cons_val_three,
        Matrix.head_cons,Matrix.tail_cons,Complex.star_def,map_div₀,map_ofNat,U,mats,pauliMatrix,qubitX,qubitZ,Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply,Matrix.kroneckerMap_apply,Matrix.ofNat_apply,Complex.ext_iff]
  let S : Subgroup (Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ) :=
    { carrier := Set.range U
      one_mem' := ⟨0,Subtype.ext rfl⟩
      mul_mem' := by rintro _ _ ⟨k,rfl⟩ ⟨l,rfl⟩; exact ⟨table k l,(hmul k l).symm⟩
      inv_mem' := by rintro _ ⟨k,rfl⟩; exact ⟨k,(hinv k).symm⟩ }
  have hu : Function.Injective U := by
    intro k l h
    have hentry := congrArg (fun g : Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ =>
      ((g.val (0,0) (0,0)).re, (g.val (0,0) (1,1)).im,
        (g.val (0,0) (1,0)).im)) h
    fin_cases k <;> fin_cases l <;> first | rfl |
      norm_num [Matrix.vecMul,dotProduct,Matrix.cons_val_two,Matrix.cons_val_three,
        Matrix.head_cons,Matrix.tail_cons,Complex.star_def,map_div₀,map_ofNat,U,mats,pauliMatrix,qubitX,qubitZ,Matrix.kroneckerMap_apply,
        Matrix.ofNat_apply] at hentry
  have hfix (k : Fin 4) : (U k).val *ᵥ entVector = entVector := by
    fin_cases k <;> ext i
    all_goals rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.vecMul,dotProduct,Matrix.cons_val_two,Matrix.cons_val_three,
        Matrix.head_cons,Matrix.tail_cons,Complex.ext_iff,Complex.mul_re,Complex.mul_im,Complex.star_def,map_div₀,map_ofNat,U,mats,entVector,pauliMatrix,qubitX,qubitZ,Matrix.mulVec,dotProduct,
        Fintype.sum_prod_type,Fin.sum_univ_two,Matrix.kroneckerMap_apply,Matrix.ofNat_apply]
  refine ⟨S,entVector,?_,?_,?_,?_,?_,rfl⟩
  · rintro ⟨g,hg⟩
    obtain ⟨k,rfl⟩ := hg
    fin_cases k
    · exact ⟨1,by simp,.I,.I,by simp [U,mats,pauliMatrix]⟩
    · exact ⟨1,by simp,.X,.Y,by simp [U,mats]⟩
    · exact ⟨1,by simp,.Y,.Z,by simp [U,mats]⟩
    · exact ⟨-1,by simp,.Z,.X,by simp [U,mats]⟩
  · change Nat.card (Set.range U) = Fintype.card (Fin 2 × Fin 2)
    rw [← Nat.card_congr (Equiv.ofInjective U hu)]; simp
  · rintro ⟨g,hg⟩ ⟨h,hh⟩; obtain ⟨k,rfl⟩ := hg; obtain ⟨l,rfl⟩ := hh
    apply Subtype.ext
    change U k * U l = U l * U k
    rw [hmul,hmul]; congr 1
    fin_cases k <;> fin_cases l <;> rfl
  · norm_num [Matrix.vecMul,dotProduct,Matrix.cons_val_two,Matrix.cons_val_three,
        Matrix.head_cons,Matrix.tail_cons,Complex.star_def,map_div₀,map_ofNat,entVector,Fintype.sum_prod_type,Fin.sum_univ_two,
      ← Complex.normSq_eq_norm_sq,Complex.normSq,Complex.mul_re,Complex.mul_im]
  · intro v; constructor
    · intro hv
      have hp := hv ⟨U 1,1,rfl⟩; have hq := hv ⟨U 2,2,rfl⟩
      have hpzero := congrFun hp (0,0); have hpone := congrFun hp (0,1)
      have hqzero := congrFun hq (0,0)
      norm_num [Matrix.vecMul,dotProduct,Matrix.cons_val_two,Matrix.cons_val_three,
        Matrix.head_cons,Matrix.tail_cons,Complex.star_def,map_div₀,map_ofNat,U,mats,pauliMatrix,qubitX,qubitZ,Matrix.mulVec,dotProduct,
        Fintype.sum_prod_type,Fin.sum_univ_two,Matrix.kroneckerMap_apply] at hpzero hpone hqzero
      refine ⟨2*v (0,0),?_⟩
      ext i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;>
        norm_num [entVector,Pi.smul_apply,smul_eq_mul]
      · ring
      · linear_combination -hpone - hqzero
      · linear_combination (norm := (ring_nf; simp)) Complex.I * hqzero
      · linear_combination (norm := (ring_nf; simp)) Complex.I * hpzero
    · rintro ⟨c,rfl⟩ ⟨g,hg⟩; obtain ⟨k,rfl⟩ := hg
      simp only [Matrix.mulVec_smul,hfix]

private theorem density_witnesses : IsDensity rhoA ∧ IsDensity rhoB ∧ IsDensity sigma := by
  have pure (ρ : QubitMatrix) (hm : ρ * ρᴴ = ρ) (ht : ρ.trace = 1) : IsDensity ρ :=
    ⟨hm ▸ Matrix.posSemidef_self_mul_conjTranspose ρ,ht⟩
  refine ⟨pure rhoA ?_ ?_,pure rhoB ?_ ?_,pure sigma ?_ ?_⟩
  all_goals first
  | solve | norm_num [Matrix.vecMul,dotProduct,Matrix.cons_val_two,Matrix.cons_val_three,
        Matrix.head_cons,Matrix.tail_cons,Complex.star_def,map_div₀,map_ofNat,rhoA,rhoB,sigma,Matrix.trace,Fin.sum_univ_two]
  | ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.vecMul,dotProduct,Matrix.cons_val_two,Matrix.cons_val_three,
        Matrix.head_cons,Matrix.tail_cons,Complex.star_def,map_div₀,map_ofNat,rhoA,rhoB,sigma,Matrix.mul_apply,Fin.sum_univ_two,
        Matrix.conjTranspose_apply,Complex.ext_iff]

private theorem equatorial_values : bloch rhoA .Z = 0 ∧ bloch rhoB .Z = 0 ∧
    COne rhoA = 1/5 ∧ COne rhoB = 2/13 := by
  have za : bloch rhoA .Z = 0 := by
    norm_num [Matrix.vecMul,dotProduct,Matrix.cons_val_two,Matrix.cons_val_three,
        Matrix.head_cons,Matrix.tail_cons,Complex.star_def,map_div₀,map_ofNat,bloch,rhoA,pauliMatrix,qubitZ,Matrix.mul_apply,Matrix.trace,Fin.sum_univ_two]
  have zb : bloch rhoB .Z = 0 := by
    norm_num [Matrix.vecMul,dotProduct,Matrix.cons_val_two,Matrix.cons_val_three,
        Matrix.head_cons,Matrix.tail_cons,Complex.star_def,map_div₀,map_ofNat,bloch,rhoB,pauliMatrix,qubitZ,Matrix.mul_apply,Matrix.trace,Fin.sum_univ_two]
  have ha := (distance_one_nonpositive rhoA density_witnesses.1 (by rw [za]; simp)).choose_spec.2.2.2
  have hb := (distance_one_nonpositive rhoB density_witnesses.2.1 (by rw [zb]; simp)).choose_spec.2.2.2
  refine ⟨za,zb,?_,?_⟩
  · rw [ha]; norm_num [Matrix.vecMul,dotProduct,Matrix.cons_val_two,Matrix.cons_val_three,
        Matrix.head_cons,Matrix.tail_cons,Complex.star_def,map_div₀,map_ofNat,PiLp.norm_eq_of_L1,PiLp.toLp_apply,Real.norm_eq_abs,
      WignerOne,Wigner,phasePoint,rhoA,pauliMatrix,qubitX,qubitZ,Matrix.trace,
      Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_two,Matrix.ofNat_apply]
  · rw [hb]; norm_num [Matrix.vecMul,dotProduct,Matrix.cons_val_two,Matrix.cons_val_three,
        Matrix.head_cons,Matrix.tail_cons,Complex.star_def,map_div₀,map_ofNat,PiLp.norm_eq_of_L1,PiLp.toLp_apply,Real.norm_eq_abs,
      WignerOne,Wigner,phasePoint,rhoB,pauliMatrix,qubitX,qubitZ,Matrix.trace,
      Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_two,Matrix.ofNat_apply]

private theorem sigma_value : COne sigma = 2/9 := by
  let sign : PhasePoint → ℝ := fun a => if a = (0,0) then 1 else -1
  have freebound : ∀ v ∈ Wfree phasePoint pauliSet, (∑ a, sign a*v a) ≤ 0 := by
    apply convexHull_min
    · rintro _ ⟨τ,hτ,rfl⟩
      change (∑ a, sign a * WignerOne τ a) ≤ 0
      obtain ⟨p,e,hp,rfl⟩ := stabilizer_one_classification τ hτ
      cases p <;> try contradiction
      all_goals fin_cases e <;>
        norm_num [Matrix.vecMul,dotProduct,Matrix.cons_val_two,Matrix.cons_val_three,
        Matrix.head_cons,Matrix.tail_cons,Complex.star_def,map_div₀,map_ofNat,sign,WignerOne,Wigner,phasePoint,spectral,pauliMatrix,qubitX,qubitZ,
          Matrix.trace,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_two,Matrix.ofNat_apply]
    · intro x hx y hy a b ha hb hab
      change (∑ i, sign i * (a*x i+b*y i)) ≤ 0
      have he : (∑ i, sign i * (a*x i+b*y i)) =
          a*(∑ i, sign i*x i)+b*(∑ i, sign i*y i) := by
        simp only [Finset.mul_sum,← Finset.sum_add_distrib]; congr 1; ext i; ring
      rw [he]; exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hx)
        (mul_nonpos_of_nonneg_of_nonpos hb hy)
  have lower : 2/9 ≤ COne sigma := by
    obtain ⟨v,hv,heq,_⟩ := COne_min sigma
    have hpt (a : PhasePoint) : sign a * (WignerOne sigma a-v a) ≤
        |WignerOne sigma a-v a| := by
      dsimp [sign]; split_ifs
      · rw [one_mul]; exact le_abs_self _
      · rw [neg_one_mul]; exact neg_le_abs _
    have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hpt a)
    have heval : (∑ a, sign a * WignerOne sigma a) = 2/9 := by
      norm_num [Matrix.vecMul,dotProduct,Matrix.cons_val_two,Matrix.cons_val_three,
        Matrix.head_cons,Matrix.tail_cons,Complex.star_def,map_div₀,map_ofNat,sign,WignerOne,Wigner,phasePoint,sigma,pauliMatrix,qubitX,qubitZ,
        Matrix.trace,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_two,Matrix.ofNat_apply]
    rw [heq,PiLp.norm_eq_of_L1]
    simp only [PiLp.toLp_apply,Real.norm_eq_abs,Pi.sub_apply] at *
    simp only [mul_sub,Finset.sum_sub_distrib,heval] at hsum
    linarith [freebound v hv]
  have upper : COne sigma ≤ 2/9 := by
    let y := WignerOne (spectral .Y 0); let z := WignerOne (spectral .Z 0)
    have hy : y ∈ Wfree phasePoint pauliSet :=
      subset_convexHull ℝ _ ⟨_,(spectral_stabilizer .Y 0 (by decide)).1,rfl⟩
    have hz : z ∈ Wfree phasePoint pauliSet :=
      subset_convexHull ℝ _ ⟨_,(spectral_stabilizer .Z 0 (by decide)).1,rfl⟩
    have hv : (1/3 : ℝ) • y + (2/3 : ℝ) • z ∈ Wfree phasePoint pauliSet :=
      (convex_convexHull ℝ _) hy hz (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨v,hv',_,hmin⟩ := COne_min sigma
    have h := hmin _ hv
    norm_num [Matrix.vecMul,dotProduct,Matrix.cons_val_two,Matrix.cons_val_three,
        Matrix.head_cons,Matrix.tail_cons,Complex.star_def,map_div₀,map_ofNat,y,z,PiLp.norm_eq_of_L1,PiLp.toLp_apply,Real.norm_eq_abs,
      Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,WignerOne,Wigner,phasePoint,
      sigma,spectral,pauliMatrix,qubitX,qubitZ,Matrix.trace,Matrix.mul_apply,
      Fintype.sum_prod_type,Fin.sum_univ_two,Matrix.ofNat_apply] at h
    exact h
  exact le_antisymm upper lower

private def mixtureStates : Fin 5 → TwoQubitMatrix :=
  ![spectral .X 0 ⊗ₖ spectral .Y 0,spectral .Y 0 ⊗ₖ spectral .Y 0,
    spectral .X 0 ⊗ₖ spectral .Z 0,spectral .Y 0 ⊗ₖ spectral .Z 0,entangled]
private def mixture (weights : Fin 5 → ℝ) : PhasePoint × PhasePoint → ℝ :=
  ∑ k, weights k • WignerTwo (mixtureStates k)

private theorem mixture_free (weights : Fin 5 → ℝ) (hn : ∀ k, 0 ≤ weights k)
    (hs : ∑ k, weights k = 1) : mixture weights ∈ Wfree phasePointTwo pauliTwo := by
  apply (convex_convexHull ℝ _).sum_mem (fun k _ => hn k) hs
  intro k _; apply subset_convexHull ℝ _
  refine ⟨mixtureStates k,?_,rfl⟩
  fin_cases k
  · exact spectral_product_stabilizer .X .Y 0 0 (by decide) (by decide)
  · exact spectral_product_stabilizer .Y .Y 0 0 (by decide) (by decide)
  · exact spectral_product_stabilizer .X .Z 0 0 (by decide) (by decide)
  · exact spectral_product_stabilizer .Y .Z 0 0 (by decide) (by decide)
  · exact entangled_stabilizer

private theorem joint_lower (ρ : TwoQubitMatrix) :
    (∑ a, (dual a : ℝ) * WignerTwo ρ a) - 1/2 ≤ CTwo ρ := by
  obtain ⟨v,hv,heq,_⟩ := CTwo_min ρ
  have hsign (a : PhasePoint × PhasePoint) : (dual a : ℝ) = 1 ∨ (dual a : ℝ) = -1 := by
    rcases a with ⟨⟨i,j⟩,⟨k,l⟩⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num [Matrix.vecMul,dotProduct,Matrix.cons_val_two,Matrix.cons_val_three,
        Matrix.head_cons,Matrix.tail_cons,Complex.star_def,map_div₀,map_ofNat,dual,finProdFinEquiv]
  have hpt (a : PhasePoint × PhasePoint) : (dual a : ℝ) * (WignerTwo ρ a-v a) ≤
      |WignerTwo ρ a-v a| := by
    rcases hsign a with h | h
    · rw [h,one_mul]; exact le_abs_self _
    · rw [h,neg_one_mul]; exact neg_le_abs _
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hpt a)
  rw [heq,PiLp.norm_eq_of_L1]
  simp only [PiLp.toLp_apply,Real.norm_eq_abs,Pi.sub_apply] at *
  simp only [mul_sub,Finset.sum_sub_distrib] at hsum
  linarith [dual_free_bound v hv]

private theorem joint_values : CTwo (rhoA ⊗ₖ sigma) = 7/18 ∧
    CTwo (rhoB ⊗ₖ sigma) = 79/234 := by
  let qa : Matrix (Fin 4) (Fin 4) ℝ :=
    !![11/30,1/5,-1/30,1/15; -11/180,-1/30,1/180,-1/90;
       11/90,1/15,-1/90,1/45; 11/60,1/10,-1/60,1/30]
  let qb : Matrix (Fin 4) (Fin 4) ℝ :=
    !![55/156,5/26,-5/156,5/78; -11/234,-1/39,1/234,-1/117;
       11/156,1/26,-1/156,1/78; 55/234,5/39,-5/234,5/117]
  have hqa (a : PhasePoint × PhasePoint) : WignerTwo (rhoA ⊗ₖ sigma) a =
      qa (finProdFinEquiv a.1) (finProdFinEquiv a.2) := by
    rcases a with ⟨⟨i,j⟩,⟨k,l⟩⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num [qa,finProdFinEquiv,WignerTwo,Wigner,phasePointTwo,phasePoint,
        rhoA,sigma,pauliMatrix,qubitX,qubitZ,Matrix.trace,Matrix.mul_apply,
        Fintype.sum_prod_type,Fin.sum_univ_two,Matrix.kroneckerMap_apply,Matrix.ofNat_apply]
  have hqb (a : PhasePoint × PhasePoint) : WignerTwo (rhoB ⊗ₖ sigma) a =
      qb (finProdFinEquiv a.1) (finProdFinEquiv a.2) := by
    rcases a with ⟨⟨i,j⟩,⟨k,l⟩⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num [qb,finProdFinEquiv,WignerTwo,Wigner,phasePointTwo,phasePoint,
        rhoB,sigma,pauliMatrix,qubitX,qubitZ,Matrix.trace,Matrix.mul_apply,
        Fintype.sum_prod_type,Fin.sum_univ_two,Matrix.kroneckerMap_apply,Matrix.ofNat_apply]
  let coords : Fin 5 → Matrix (Fin 4) (Fin 4) ℝ :=
    ![!![4,0,0,4;0,0,0,0;4,0,0,4;0,0,0,0],
      !![4,0,0,4;0,0,0,0;0,0,0,0;4,0,0,4],
      !![4,4,0,0;0,0,0,0;4,4,0,0;0,0,0,0],
      !![4,4,0,0;0,0,0,0;0,0,0,0;4,4,0,0],
      !![2,2,-2,2;-2,2,2,2;2,-2,2,2;2,2,2,-2]]
  have hcoords (k : Fin 5) (a : PhasePoint × PhasePoint) :
      WignerTwo (mixtureStates k) a = coords k (finProdFinEquiv a.1) (finProdFinEquiv a.2)/16 := by
    rcases a with ⟨⟨i,j⟩,⟨l,m⟩⟩
    fin_cases k <;> fin_cases i <;> fin_cases j <;> fin_cases l <;> fin_cases m <;>
      norm_num [coords,finProdFinEquiv,mixtureStates,entangled,entVector,
        WignerTwo,Wigner,phasePointTwo,phasePoint,spectral,pauliMatrix,qubitX,qubitZ,
        Matrix.trace,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_two,
        Matrix.kroneckerMap_apply,Matrix.vecMulVec,Matrix.ofNat_apply,
        Complex.star_def,map_div₀,map_ofNat,Matrix.cons_val_two,Matrix.cons_val_three,
        Matrix.head_cons,Matrix.tail_cons]
  have la := joint_lower (rhoA ⊗ₖ sigma)
  have lb := joint_lower (rhoB ⊗ₖ sigma)
  simp only [hqa,hqb] at la lb
  norm_num [dual,qa,qb,finProdFinEquiv,Fintype.sum_prod_type,Fin.sum_univ_two] at la lb
  let wa : Fin 5 → ℝ := ![1/15,8/45,1/3,17/45,2/45]
  let wb : Fin 5 → ℝ := ![4/117,8/39,3/13,58/117,4/117]
  have fa := mixture_free wa (by intro k; fin_cases k <;> norm_num [wa])
    (by norm_num [wa,Fin.sum_univ_succ])
  have fb := mixture_free wb (by intro k; fin_cases k <;> norm_num [wb])
    (by norm_num [wb,Fin.sum_univ_succ])
  obtain ⟨v,hv,_,hmin⟩ := CTwo_min (rhoA ⊗ₖ sigma)
  have ua := hmin _ fa
  obtain ⟨v',hv',_,hmin'⟩ := CTwo_min (rhoB ⊗ₖ sigma)
  have ub := hmin' _ fb
  simp only [PiLp.norm_eq_of_L1,Real.norm_eq_abs,PiLp.toLp_apply,Pi.sub_apply,
    mixture,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,hqa,hqb,hcoords] at ua ub
  norm_num [wa,wb,qa,qb,coords,finProdFinEquiv,Fintype.sum_prod_type,
    Fin.sum_univ_two,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.head_cons,Matrix.tail_cons] at ua ub
  exact ⟨le_antisymm ua la,le_antisymm ub lb⟩

theorem result : ¬ claim := by
  rintro ⟨f,hf⟩
  have spos : 0 < bloch sigma .X * bloch sigma .Y * bloch sigma .Z := by
    norm_num [Matrix.vecMul,dotProduct,Matrix.cons_val_two,Matrix.cons_val_three,
        Matrix.head_cons,Matrix.tail_cons,Complex.star_def,map_div₀,map_ofNat,bloch,sigma,pauliMatrix,qubitX,qubitZ,Matrix.trace,Matrix.mul_apply,
      Fin.sum_univ_two]
  have ha := hf rhoA sigma density_witnesses.1 equatorial_values.1
    (by rw [equatorial_values.2.2.1]; norm_num) density_witnesses.2.2 spos
  have hb := hf rhoB sigma density_witnesses.2.1 equatorial_values.2.1
    (by rw [equatorial_values.2.2.2]; norm_num) density_witnesses.2.2 spos
  rw [deficit,equatorial_values.2.2.1,sigma_value,joint_values.1] at ha
  rw [deficit,equatorial_values.2.2.2,sigma_value,joint_values.2] at hb
  linarith
#print axioms result
end D5.S3.Quantum.Magic.QubitWignerDeficitFactorRefutation
