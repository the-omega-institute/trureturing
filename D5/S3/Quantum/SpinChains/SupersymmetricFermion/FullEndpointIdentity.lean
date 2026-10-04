/- GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/FullEndpointIdentity
   generality: I
   mirror-B: D5/B/S3/Quantum/SpinChains/SupersymmetricFermion/FullEndpointIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A period-three anticommutator reduces to endpoint occupations. -/
/-
full_symmetrized_diagonal:
  proof_shape: content
  escape_witness: full_symmetrized_diagonal (form 2): Localization of cubic products and cancellation of hopping currents leave the full-space occupation diagonal.
  Direct frozen dependencies: Assignment, tensorOp, qubitZ, visibleProjector, localOp, antiAd.
admission_basis: escape-witness
Chain dependencies: D5.S3.Quantum.SpinChains.SupersymmetricFermion.CubicCompression; freeze in topological import order.
Information-escape registration is paused under CLAUDE.md §3.9.
-/
import D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion
import D5.S3.Quantum.SpinChains.SupersymmetricFermion.CubicCompression
set_option linter.unusedSimpArgs false
open scoped BigOperators Matrix Classical
set_option quotPrecheck false in
local notation "tensorOp" => (fun {N : ℕ} (w : Fin N → Matrix Bool Bool ℂ) =>
  Matrix.submatrix
    (D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp (n := N)
      (fun i => Matrix.submatrix (w i) finTwoEquiv finTwoEquiv))
    (fun (s : Fin N → Bool) (i : Fin N) => finTwoEquiv.symm (s i))
    (fun (s : Fin N → Bool) (i : Fin N) => finTwoEquiv.symm (s i)))
open PredictiveThermodynamic.Physical (Assignment visibleProjector)
open D5.S3.Quantum.FiniteDimensional (qubitZ)
local notation "spinZ" => (qubitZ.submatrix finTwoEquiv.symm finTwoEquiv.symm)
local notation "spinP" => ((1 : Matrix Bool Bool ℂ) - visibleProjector)
namespace D5.S3.Quantum.SpinChains.SupersymmetricFermion.FullEndpointIdentity
noncomputable section
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.DressedOperators
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.SuperchargeProducts
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.CubicProducts
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.HoppingProducts
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreModel
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.CubicCompression
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
theorem full_symmetrized_diagonal (N : ℕ) (hN : 3≤N) (hm : N%3=0) (a b cc : ℝ) : symOp (((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)) (D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion.antiAd ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm (fullQ (fun i : Fin N => chainG a b cc i.val))) ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm (fullR N a b cc))))) = ((2*a^2*cc^2 : ℝ) : ℂ) • (fullPAt N 1 - fullPAt N (N-2)) + ∑ k : Fin (N-2), blockDiagonal a b cc (⟨k.val,by omega⟩ : Fin N) (by dsimp; omega):= by
  have localOp_as_tensor {N : ℕ} (i : Fin N) :
      ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp i (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) = tensorOp (numberWord i) := by
    classical
    ext s t
    simp only [D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp, D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp,
      Matrix.submatrix_apply, Matrix.of_apply]
    apply Finset.prod_congr rfl
    intro k _
    by_cases h : k = i
    · subst k
      simp [Function.update_self, numberWord, sub_sub_cancel]
    · simp [Function.update_of_ne h, numberWord, h, Matrix.one_apply, Equiv.apply_eq_iff_eq]
  have antiAd_reindexed {N : ℕ} (A B : FullOperator N) :
      ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)) (D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion.antiAd ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm A) ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm B))) = A * B + B * A := by
    simp only [D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion.antiAd, map_add, map_mul, AlgEquiv.apply_symm_apply]
  let tensorProduct {N : ℕ} (w : Fin N → Local) : FullOperator N := tensorOp w
  have tensorOp_entries {N : ℕ} (w : Fin N → Local) : tensorProduct w = (fun s t => ∏ i : Fin N, w i (s i) (t i)) := by
    ext s t
    simp [tensorProduct, D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp,
      Matrix.submatrix_apply]
  have spinP_def : spinP = Matrix.diagonal (fun b => if b then (0 : ℂ) else 1) := by
    ext s t
    cases s <;> cases t <;> norm_num [visibleProjector, Matrix.diagonal, Matrix.sub_apply]
  have periodThree_periodic (a b cc : ℝ) (j : ℕ) : periodThree a b cc (j + 3) = periodThree a b cc j := by simp [periodThree, Nat.add_mod]
  have symOp_add {N : ℕ} (A B : FullOperator N) : symOp (A+B) = symOp A + symOp B := by
    simp only [symOp,Matrix.conjTranspose_add]
    abel
  have antiOp_add {N : ℕ} (Q A B : FullOperator N) : ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)) (D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion.antiAd ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm Q) ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm (A+B)))) = ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)) (D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion.antiAd ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm Q) ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm A))) + ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)) (D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion.antiAd ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm Q) ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm B))) := by
    simp only [antiAd_reindexed,mul_add,add_mul]
    abel
  have matrix_real_smul_eq_complex {N : ℕ} (z : ℝ) (A : FullOperator N) : z • A = (z : ℂ) • A := by
    ext s t
    simp only [Matrix.smul_apply,Pi.smul_apply,smul_eq_mul,Complex.real_smul]
  have fullR_blocks (N : ℕ) (hN : 0<N) (a b cc : ℝ) : fullR N a b cc = fullBoundary N a b cc + ∑ k : Fin (N-2), blockR a b cc (⟨k.val,by omega⟩ : Fin N) (by dsimp; omega) := by
    classical
    unfold fullR fullBoundary; rw [dif_pos hN,dif_pos hN]
    simp only [blockR,chainG,matrix_real_smul_eq_complex,
      Finset.smul_sum,Finset.sum_add_distrib,Finset.sum_sub_distrib,Nat.add_assoc]
    abel
  have antiOp_sum {N : ℕ} {ι : Type} (s : Finset ι) (Q : FullOperator N) (f : ι → FullOperator N) : ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)) (D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion.antiAd ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm Q) ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm (∑ i ∈ s, f i)))) = ∑ i ∈ s, ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)) (D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion.antiAd ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm Q) ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm (f i)))) := by simp only [antiAd_reindexed,Finset.mul_sum,Finset.sum_mul,Finset.sum_add_distrib]
  have symOp_sum {N : ℕ} {ι : Type} (s : Finset ι) (f : ι → FullOperator N) : symOp (∑ i ∈ s, f i) = ∑ i ∈ s, symOp (f i) := by simp only [symOp,Matrix.conjTranspose_sum,Finset.sum_add_distrib]
  have symOp_real_smul {N : ℕ} (z : ℝ) (A : FullOperator N) : symOp ((z : ℂ) • A) = (z : ℂ) • symOp A := by simp [symOp,Matrix.conjTranspose_smul,smul_add]
  have antiOp_smul {N : ℕ} (z : ℂ) (Q A : FullOperator N) : ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)) (D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion.antiAd ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm Q) ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm (z • A)))) = z • ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)) (D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion.antiAd ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm Q) ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm A))) := by simp only [antiAd_reindexed,Matrix.smul_mul,Matrix.mul_smul,smul_add]
  have symOp_sub {N : ℕ} (A B : FullOperator N) : symOp (A-B) = symOp A - symOp B := by
    simp only [symOp,Matrix.conjTranspose_sub]
    abel
  have sum_fin_at {α : Type} [AddCommMonoid α] {N : ℕ} (f : Fin N → α) (k : ℕ) : (∑ i : Fin N, if i.val=k then f i else 0) = if hk : k<N then f ⟨k,hk⟩ else 0 := by
    classical
    by_cases hk : k<N
    · rw [dif_pos hk]
      rw [Finset.sum_eq_single (⟨k,hk⟩ : Fin N)]
      · simp
      · intro i _hi hne
        have hv : i.val ≠ k := by intro hh; exact hne (Fin.ext hh)
        simp [hv]
      · simp
    · rw [dif_neg hk]
      apply Finset.sum_eq_zero
      intro i _hi
      have hv : i.val ≠ k := by intro hh; rw [← hh] at hk; exact hk i.isLt
      simp [hv]
  have sum_fin_before {α : Type} [AddCommMonoid α] {N : ℕ} (f : Fin N → α) (j : Fin N) : (∑ i : Fin N, if i.val+1=j.val then f i else 0) = if hj : 0<j.val then f ⟨j.val-1,by omega⟩ else 0 := by
    classical
    by_cases hj : 0<j.val
    · rw [dif_pos hj]
      have he (i : Fin N) : i.val+1=j.val ↔ i.val=j.val-1 := by omega
      simp_rw [he]; rw [sum_fin_at,dif_pos (show j.val-1<N by omega)]
    · rw [dif_neg hj]
      apply Finset.sum_eq_zero
      intro i _hi
      have hn : ¬i.val+1=j.val := by omega
      simp [hn]
  have fullQ_split_explicit {N : ℕ} (g : ℕ → ℝ) (j : Fin N) (hr : j.val+2<N) : ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)) (D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion.antiAd ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm (fullQ (fun i : Fin N => g i.val))) ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm (fullSplit j)))) = (if 0<j.val then (g (j.val-1) : ℂ) • (fullFourHop N (j.val-1))ᴴ else 0) + (g j.val : ℂ) • ((fullHop N (j.val+1))ᴴ * fullLeftP N j.val) - (g (j.val+2) : ℂ) • (fullHop N j.val * fullPAt N (j.val+3)) - (g (j.val+3) : ℂ) • fullFourHop N j.val := by
    classical
    rw [antiAd_reindexed,fullQ_split_localized (fun i : Fin N => g i.val) j hr]
    have ht (i : Fin N) : (g i.val : ℂ) • (if i.val+1=j.val then fullSplit j * fullD i else if i.val=j.val ∨ i.val=j.val+2 then fullD i * fullSplit j else if i.val=j.val+3 then fullSplit j * fullD i else 0) = (if i.val+1=j.val then (g i.val : ℂ) • (fullFourHop N (j.val-1))ᴴ else 0) + (if i.val=j.val then (g i.val : ℂ) • ((fullHop N (j.val+1))ᴴ * fullLeftP N j.val) else 0) + (if i.val=j.val+2 then (g i.val : ℂ) • -(fullHop N j.val * fullPAt N (j.val+3)) else 0) + (if i.val=j.val+3 then (g i.val : ℂ) • -(fullFourHop N j.val) else 0) := by
      by_cases hp : i.val+1=j.val
      · have hi : i = (⟨j.val-1,by omega⟩ : Fin N) := Fin.ext (by change i.val = j.val-1; omega)
        have h0 : 0<j.val := by omega
        simp (disch := omega) only [hp,if_pos,if_neg,add_zero,zero_add]; rw [hi,split_before j hr h0]; simp
      · by_cases h0 : i.val=j.val
        · have hi : i=j := Fin.ext h0
          subst i
          simp (disch := omega) [split_at_left j hr]
        · by_cases h2 : i.val=j.val+2
          · have hi : i=(⟨j.val+2,hr⟩ : Fin N) := Fin.ext h2
            simp (disch := omega) only [hp,h0,h2,if_pos,if_neg,zero_add,add_zero]; rw [hi,split_at_right j hr]; simp
          · by_cases h3 : i.val=j.val+3
            · have hh : j.val+3<N := by omega
              have hi : i=(⟨j.val+3,hh⟩ : Fin N) := Fin.ext h3
              simp (disch := omega) only [hp,h0,h2,h3,if_pos,if_neg,zero_add,add_zero]; rw [hi,split_after j hh]; simp
            · simp [hp,h0,h2,h3]
    simp_rw [ht]; simp only [Finset.sum_add_distrib]; rw [sum_fin_before,sum_fin_at,sum_fin_at,sum_fin_at]; rw [dif_pos (show j.val<N from j.isLt),dif_pos hr]
    split_ifs with h0 h3 <;> simp only [smul_neg,sub_eq_add_neg]
    all_goals simp (disch := omega) [fullFourHop]
    all_goals omega
  have tensorOp_adjoint {N : ℕ} (w : Fin N → Local) : (tensorProduct w)ᴴ = tensorProduct (fun i => (w i)ᴴ) := by
    classical
    rw [tensorOp_entries, tensorOp_entries]
    ext s t
    change star (∏ i : Fin N, w i (t i) (s i)) = ∏ i : Fin N, star (w i (t i) (s i))
    simp
  have spinP_self_adjoint : spinPᴴ = spinP := by
    ext s t
    cases s <;> cases t <;> simp [spinP_def, visibleProjector, Matrix.conjTranspose_apply]
  have fullLeftP_self_adjoint (N k : ℕ) : (fullLeftP N k)ᴴ = fullLeftP N k := by
    unfold fullLeftP; rw [tensorOp_adjoint]
    congr 1
    funext i
    split_ifs <;> simp [spinP_self_adjoint]
  have tensorOp_mul {N : ℕ} (u v : Fin N → Local) : tensorProduct u * tensorProduct v = tensorProduct (fun i => u i * v i) := by
    classical
    rw [tensorOp_entries, tensorOp_entries, tensorOp_entries]
    ext s t
    change (∑ x : Assignment N, (∏ i : Fin N, u i (s i) (x i)) * (∏ i : Fin N, v i (x i) (t i))) =
      ∏ i : Fin N, ∑ b : Bool, u i (s i) b * v i b (t i)
    simp_rw [← Finset.prod_mul_distrib]; exact (Fintype.prod_sum (fun i b => u i (s i) b * v i b (t i))).symm
  have fullHop_LeftP_commute (N j : ℕ) : fullHop N (j+1) * fullLeftP N j = fullLeftP N j * fullHop N (j+1) := by
    classical
    by_cases hr : j+1+1<N
    · simp only [fullHop,if_pos hr,fullLeftP]
      rw [tensorOp_mul,tensorOp_mul]
      congr 1
      funext i
      by_cases hi : i.val+1=j
      · have hd : hopWord (j+1) i = 1 := by
          simp (disch := omega) only [hopWord,if_pos,if_neg]
        simp [hi,hd]
      · simp [hi]
    · simp [fullHop,hr]
  have symOp_hop_leftP (N j : ℕ) : symOp ((fullHop N (j+1))ᴴ * fullLeftP N j) = symOp (fullHop N (j+1)) * fullLeftP N j := by
    have hc := fullHop_LeftP_commute N j
    simp only [symOp,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,
      fullLeftP_self_adjoint]
    rw [← hc]
    noncomm_ring
  have fullPAt_self_adjoint (N k : ℕ) : (fullPAt N k)ᴴ = fullPAt N k := by
    unfold fullPAt; rw [tensorOp_adjoint]
    congr 1
    funext i
    split_ifs <;> simp [spinP_self_adjoint]
  have symOp_hop_rightP (N j : ℕ) : symOp (fullHop N j * fullPAt N (j+3)) = symOp (fullHop N j) * fullPAt N (j+3) := by
    have hc := fullHop_PAt_commute N j (j+3) (by omega) (by omega)
    have hca := congrArg Matrix.conjTranspose hc
    simp only [Matrix.conjTranspose_mul,fullPAt_self_adjoint] at hca; simp only [symOp,Matrix.conjTranspose_mul,fullPAt_self_adjoint]; rw [hca]
    noncomm_ring
  have symOp_adjoint {N : ℕ} (A : FullOperator N) : symOp Aᴴ = symOp A := by
    simp only [symOp,Matrix.conjTranspose_conjTranspose]
    abel
  have fullQ_split_symmetric {N : ℕ} (g : ℕ → ℝ) (j : Fin N) (hr : j.val+2<N) : symOp (((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)) (D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion.antiAd ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm (fullQ (fun i : Fin N => g i.val))) ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm (fullSplit j))))) = (if 0<j.val then (g (j.val-1) : ℂ) • symOp (fullFourHop N (j.val-1)) else 0) + (g j.val : ℂ) • (symOp (fullHop N (j.val+1)) * fullLeftP N j.val) - (g (j.val+2) : ℂ) • (symOp (fullHop N j.val) * fullPAt N (j.val+3)) - (g (j.val+3) : ℂ) • symOp (fullFourHop N j.val) := by
    rw [fullQ_split_explicit g j hr]; simp only [symOp_sub,symOp_add,symOp_real_smul,symOp_hop_leftP,symOp_hop_rightP]
    have hz : symOp (0 : FullOperator N) = 0 := by simp [symOp]
    split_ifs <;> simp only [symOp_real_smul,symOp_adjoint,hz]
  have fullQ_number_commutator {N : ℕ} (coupling : Fin N → ℝ) (j : Fin N) : fullQ coupling * ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp j (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) - ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp j (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * fullQ coupling = (coupling j : ℂ) • fullD j := by
    classical
    unfold fullQ; rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    have ht (i : Fin N) : ((coupling i : ℂ) • fullD i) * ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp j (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) - ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp j (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * ((coupling i : ℂ) • fullD i) = if i = j then (coupling i : ℂ) • fullD i else 0 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
      by_cases hij : i = j
      · subst i
        rw [(fullD_number_same j).1,(fullD_number_same j).2]; simp
      · rw [fullD_number_commute i j hij]
        simp [hij]
    simp only [ht]; simp
  have tensorOp_zero_at {N : ℕ} (w : Fin N → Local) (i : Fin N) (h : w i = 0) : tensorProduct w = 0 := by
    classical
    rw [tensorOp_entries]
    ext s t
    change (∏ k : Fin N, w k (s k) (t k)) = 0
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h]; rfl)
  have spinA_mul_spinP : (Matrix.single false true (1 : ℂ)) * spinP = 0 := by
    ext s t
    cases s <;> cases t <;> norm_num [spinP_def, visibleProjector, Matrix.single, Matrix.mul_apply,
      Matrix.diagonal_apply, Fintype.sum_bool]
  have fullD_adjacent_order_zero {N : ℕ} (i j : Fin N) (hij : i.val + 1 = j.val) : fullD i * (fullD j)ᴴ = 0 := by
    classical
    unfold fullD; rw [tensorOp_adjoint, tensorOp_mul]
    apply tensorOp_zero_at _ i
    have hnot : ¬i.val + 1 = i.val := by omega
    have hneq : j.val ≠ i.val := by omega
    simp only [dressedWord, hnot, ite_false, lt_self_iff_false, ite_true,
      hij, hneq, spinP_self_adjoint]
    exact spinA_mul_spinP
  have fullD_far_mixed_anticomm_reverse {N : ℕ} (i j : Fin N) (hij : j.val + 1 < i.val) : fullD i * (fullD j)ᴴ + (fullD j)ᴴ * fullD i = 0 := by
    have h := congrArg Matrix.conjTranspose (fullD_far_mixed_anticomm j i hij)
    simpa only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero] using h
  have fullD_adjacent_order_zero_reverse {N : ℕ} (i j : Fin N) (hij : j.val + 1 = i.val) : fullD i * (fullD j)ᴴ = 0 := by
    have h := congrArg Matrix.conjTranspose (fullD_adjacent_order_zero j i hij)
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] using h
  have fullQ_dressed_creator {N : ℕ} (coupling : Fin N → ℝ) (j : Fin N) : fullQ coupling * (fullD j)ᴴ + (fullD j)ᴴ * fullQ coupling = (coupling j : ℂ) • tensorProduct (neighbourPWord j) + ∑ i : Fin N, if i.val + 1 = j.val ∨ j.val + 1 = i.val then (coupling i : ℂ) • ((fullD j)ᴴ * fullD i) else 0 := by
    classical
    unfold fullQ; rw [Finset.sum_mul,Finset.mul_sum,← Finset.sum_add_distrib]
    have ht (i : Fin N) : ((coupling i : ℂ) • fullD i) * (fullD j)ᴴ + (fullD j)ᴴ * ((coupling i : ℂ) • fullD i) = (if i = j then (coupling j : ℂ) • tensorProduct (neighbourPWord j) else 0) + (if i.val + 1 = j.val ∨ j.val + 1 = i.val then (coupling i : ℂ) • ((fullD j)ᴴ * fullD i) else 0) := by
      rw [Matrix.smul_mul,Matrix.mul_smul,← smul_add]
      by_cases heq : i = j
      · subst i
        rw [fullD_CAR]
        have hne : ¬j.val + 1 = j.val := by omega
        simp [hne,tensorProduct]
      · rw [if_neg heq]
        by_cases hnext : i.val + 1 = j.val
        · rw [fullD_adjacent_order_zero i j hnext]
          simp [hnext]
        · by_cases hprev : j.val + 1 = i.val
          · rw [fullD_adjacent_order_zero_reverse i j hprev]
            simp [hprev]
          · have hneVal : i.val ≠ j.val := by intro h; exact heq (Fin.ext h)
            have hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val := by omega
            rcases hfar with hfar | hfar
            · rw [fullD_far_mixed_anticomm i j hfar]
              simp [hprev,hnext]
            · rw [fullD_far_mixed_anticomm_reverse i j hfar]
              simp [hprev,hnext]
    simp only [ht,Finset.sum_add_distrib]; simp
  have fullQ_weighted_creator {N : ℕ} (coupling : Fin N → ℝ) (k j : Fin N) : fullQ coupling * (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * (fullD j)ᴴ) + (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * (fullD j)ᴴ) * fullQ coupling = (coupling k : ℂ) • (fullD k * (fullD j)ᴴ) + (coupling j : ℂ) • (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * tensorProduct (neighbourPWord j)) + ∑ i : Fin N, if i.val + 1 = j.val ∨ j.val + 1 = i.val then (coupling i : ℂ) • (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * ((fullD j)ᴴ * fullD i)) else 0 := by
    classical
    have he : fullQ coupling * (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * (fullD j)ᴴ) + (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * (fullD j)ᴴ) * fullQ coupling = (fullQ coupling * ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) - ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * fullQ coupling) * (fullD j)ᴴ + ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * (fullQ coupling * (fullD j)ᴴ + (fullD j)ᴴ * fullQ coupling) := by
      noncomm_ring
    rw [he,fullQ_number_commutator,fullQ_dressed_creator]; simp only [Matrix.smul_mul,Matrix.mul_smul,mul_add,Finset.mul_sum]; rw [← add_assoc]
    congr 1
    apply Finset.sum_congr rfl
    intro i _hi
    split_ifs <;> simp [Matrix.mul_smul]
  have antiOp_sub {N : ℕ} (Q A B : FullOperator N) : ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)) (D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion.antiAd ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm Q) ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm (A-B)))) = ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)) (D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion.antiAd ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm Q) ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm A))) - ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)) (D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion.antiAd ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm Q) ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm B))) := by
    simp only [antiAd_reindexed,mul_sub,sub_mul]
    abel
  have fullQ_weighted_pair_symmetric {N : ℕ} (coupling : Fin N → ℝ) (k j : Fin N) (w : ℝ) : symOp (((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)) (D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion.antiAd ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm (fullQ coupling)) ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm (((coupling j * w^2 : ℝ) : ℂ) • (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * (fullD j)ᴴ) - ((coupling k * w^2 : ℝ) : ℂ) • (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp j (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * (fullD k)ᴴ)))))) = ((coupling j * w^2 : ℝ) : ℂ) • symOp ((coupling j : ℂ) • (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * tensorProduct (neighbourPWord j)) + ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * creatorNeighbourTerms coupling j) - ((coupling k * w^2 : ℝ) : ℂ) • symOp ((coupling k : ℂ) • (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp j (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * tensorProduct (neighbourPWord k)) + ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp j (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * creatorNeighbourTerms coupling k) := by
    classical
    have hc (x z : Fin N) : ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)) (D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion.antiAd ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm (fullQ coupling)) ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp x (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * (fullD z)ᴴ)))) = (coupling x : ℂ) • (fullD x * (fullD z)ᴴ) + ((coupling z : ℂ) • (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp x (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * tensorProduct (neighbourPWord z)) + ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp x (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * creatorNeighbourTerms coupling z) := by
      rw [antiAd_reindexed,fullQ_weighted_creator]; simp only [creatorNeighbourTerms,Finset.mul_sum]
      have he : (∑ i : Fin N, if i.val + 1 = z.val ∨ z.val + 1 = i.val then (coupling i : ℂ) • (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp x (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * ((fullD z)ᴴ * fullD i)) else 0) = ∑ i : Fin N, ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp x (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * (if i.val + 1 = z.val ∨ z.val + 1 = i.val then (coupling i : ℂ) • ((fullD z)ᴴ * fullD i) else 0) := by
        apply Finset.sum_congr rfl
        intro i _hi
        split_ifs <;> simp [Matrix.mul_smul]
      rw [he]
      abel
    rw [antiOp_sub,antiOp_smul,antiOp_smul,hc,hc]; simp only [symOp_sub,symOp_add,symOp_real_smul]
    have hs : symOp (fullD k * (fullD j)ᴴ) = symOp (fullD j * (fullD k)ᴴ) := by
      simp only [symOp,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
      abel
    rw [hs]; simp only [smul_add,smul_smul]
    have hcoef : ((coupling j * w^2 : ℝ) : ℂ) * (coupling k : ℂ) = ((coupling k * w^2 : ℝ) : ℂ) * (coupling j : ℂ) := by push_cast; ring
    rw [hcoef]
    abel
  have fullNumber_left_hopping_explicit {N : ℕ} (g : ℕ → ℝ) (k j : Fin N) (hkj : k.val+2=j.val) : ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * creatorNeighbourTerms (fun i : Fin N => g i.val) j = (g (j.val+1) : ℂ) • (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * fullHop N j.val) := by
    rw [fullNumber_left_creator_neighbours _ k j hkj]
    have he (i : Fin N) : j.val+1=i.val ↔ i.val=j.val+1 := by omega
    simp_rw [he]; rw [sum_fin_at]
    by_cases hh : j.val+1<N
    · rw [dif_pos hh,hop_dressed j hh]
    · simp [hh,fullHop]
  have fullNumber_right_hopping_explicit {N : ℕ} (g : ℕ → ℝ) (k j : Fin N) (hkj : j.val+2=k.val) : ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * creatorNeighbourTerms (fun i : Fin N => g i.val) j = if 0<j.val then (g (j.val-1) : ℂ) • (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * (fullHop N (j.val-1))ᴴ) else 0 := by
    rw [fullNumber_right_creator_neighbours _ k j hkj,sum_fin_before]
    by_cases hh : 0<j.val
    · rw [dif_pos hh,if_pos hh]
      let i : Fin N := ⟨j.val-1,by omega⟩
      have hi : i.val+1<N := by dsimp [i]; omega
      have hij : (⟨i.val+1,hi⟩ : Fin N) = j := Fin.ext (by dsimp [i]; omega)
      have he : (fullD j)ᴴ * fullD i = (fullHop N (j.val-1))ᴴ := by
        change (fullD j)ᴴ * fullD i = (fullHop N i.val)ᴴ
        rw [hop_dressed i hi,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hij]
      exact congrArg (fun A : FullOperator N => (g (j.val-1) : ℂ) • (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * A)) he
    · rw [dif_neg hh,if_neg hh]
  have fullNumber_neighbourP_sym {N : ℕ} (k j : Fin N) : symOp (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * tensorProduct (neighbourPWord j)) = (2 : ℂ) • (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * tensorProduct (neighbourPWord j)) := by
    have hs : (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * tensorProduct (neighbourPWord j))ᴴ = ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * tensorProduct (neighbourPWord j) := by
      simp only [localOp_as_tensor]
      rw [tensorOp_mul,tensorOp_adjoint]
      congr 1
      funext i
      unfold numberWord neighbourPWord
      split_ifs <;>
        ext u v <;> cases u <;> cases v <;>
        norm_num [spinP_def, visibleProjector,Matrix.mul_apply,Matrix.sub_apply,Matrix.diagonal_apply,
          Matrix.one_apply,Matrix.conjTranspose_apply,Fintype.sum_bool]
    rw [symOp,hs,two_smul ℂ _]
  have fullNumber_self_adjoint {N : ℕ} (i : Fin N) : (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp i (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))))ᴴ = ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp i (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) := by
    simp only [localOp_as_tensor]
    rw [tensorOp_adjoint]
    congr 1
    funext k
    simp only [numberWord]
    split_ifs <;> simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,spinP_self_adjoint]
  have fullNumber_creator_commute {N : ℕ} (k j : Fin N) (h : k ≠ j) : ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * (fullD j)ᴴ = (fullD j)ᴴ * ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) := by
    have hh := congrArg Matrix.conjTranspose (fullD_number_commute j k h.symm)
    simpa only [Matrix.conjTranspose_mul,fullNumber_self_adjoint] using hh
  have fullHop_fullNumber_commute {N : ℕ} (j : ℕ) (k : Fin N) (hk0 : k.val ≠ j) (hk1 : k.val ≠ j+1) : fullHop N j * ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) = ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * fullHop N j := by
    classical
    by_cases hr : j+1<N
    · let i : Fin N := ⟨j,by omega⟩
      let m : Fin N := ⟨j+1,hr⟩
      have hki : k ≠ i := by intro hh; exact hk0 (congrArg Fin.val hh)
      have hkm : m ≠ k := by intro hh; exact hk1 (congrArg Fin.val hh.symm)
      have hi : i.val+1<N := hr
      rw [show j=i.val by rfl,hop_dressed i hi]
      change ((fullD i)ᴴ * fullD m) * ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) = ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * ((fullD i)ᴴ * fullD m)
      rw [Matrix.mul_assoc,fullD_number_commute m k hkm,← Matrix.mul_assoc,
        ← fullNumber_creator_commute k i hki,Matrix.mul_assoc]
    · simp [fullHop,hr]
  have symOp_number_hop {N : ℕ} (j : ℕ) (k : Fin N) (hk0 : k.val ≠ j) (hk1 : k.val ≠ j+1) : symOp (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * fullHop N j) = symOp (fullHop N j) * ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) := by
    have hc := fullHop_fullNumber_commute j k hk0 hk1
    simp only [symOp,Matrix.conjTranspose_mul,fullNumber_self_adjoint]; rw [← hc]
    noncomm_ring
  have symOp_number_hop_adjoint {N : ℕ} (j : ℕ) (k : Fin N) (hk0 : k.val ≠ j) (hk1 : k.val ≠ j+1) : symOp (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * (fullHop N j)ᴴ) = symOp (fullHop N j) * ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) := by
    have hc := fullHop_fullNumber_commute j k hk0 hk1
    have ha := congrArg Matrix.conjTranspose hc
    simp only [Matrix.conjTranspose_mul,fullNumber_self_adjoint] at ha
    have he : (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * fullHop N j)ᴴ = (fullHop N j)ᴴ * ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) := by simp only [Matrix.conjTranspose_mul,fullNumber_self_adjoint]
    rw [ha,← he,symOp_adjoint,symOp_number_hop j k hk0 hk1]
  have fullQ_pair_symmetric_explicit {N : ℕ} (g : ℕ → ℝ) (k : Fin N) (hr : k.val+2<N) : let j : Fin N := ⟨k.val+2,hr⟩
      symOp (((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)) (D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion.antiAd ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm (fullQ (fun i : Fin N => g i.val))) ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm (((g (k.val+2) * g (k.val+1)^2 : ℝ) : ℂ) • (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * (fullD j)ᴴ) -
         ((g k.val * g (k.val+1)^2 : ℝ) : ℂ) • (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp j (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * (fullD k)ᴴ)))))) =
        ((2 * g (k.val+2)^2 * g (k.val+1)^2 : ℝ) : ℂ) •
          (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * tensorProduct (neighbourPWord j)) -
        ((2 * g k.val^2 * g (k.val+1)^2 : ℝ) : ℂ) •
          (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp j (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * tensorProduct (neighbourPWord k)) +
        ((g (k.val+2) * g (k.val+1)^2 * g (k.val+3) : ℝ) : ℂ) •
          (symOp (fullHop N (k.val+2)) * ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)))) -
        (if 0<k.val then
          ((g k.val * g (k.val+1)^2 * g (k.val-1) : ℝ) : ℂ) •
            (symOp (fullHop N (k.val-1)) * ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp j (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)))) else 0) := by
    classical
    dsimp only
    let j : Fin N := ⟨k.val+2,hr⟩
    have hp := fullQ_weighted_pair_symmetric (fun i : Fin N => g i.val) k j (g (k.val+1))
    change symOp (((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)) (D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion.antiAd ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm _) ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm _)))) = _ at hp
    rw [hp]
    rw [fullNumber_left_hopping_explicit g k j (by dsimp [j]),
      fullNumber_right_hopping_explicit g j k (by dsimp [j])]
    simp only [symOp_add,symOp_real_smul,fullNumber_neighbourP_sym]
    by_cases hk : 0<k.val
    · rw [if_pos hk]
      simp only [symOp_real_smul]
      rw [symOp_number_hop (k.val+2) k (by omega) (by omega),
        symOp_number_hop_adjoint (k.val-1) j (by dsimp [j]; omega) (by dsimp [j]; omega),if_pos hk]
      simp only [smul_add,smul_smul]
      dsimp [j]
      push_cast; module
    · rw [if_neg hk]
      have hz : symOp (0 : FullOperator N) = 0 := by simp [symOp]
      rw [hz,symOp_number_hop (k.val+2) k (by omega) (by omega),if_neg hk]; simp only [smul_add,smul_smul,smul_zero,sub_zero,add_zero]
      dsimp [j]
      push_cast; module
  have tensorOp_one {N : ℕ} : tensorProduct (fun _ : Fin N => (1 : Local)) = (1 : FullOperator N) := by
    classical
    ext s t
    simp only [tensorOp_entries, Matrix.one_apply]
    by_cases h : s = t
    · subst t
      simp
    · rw [if_neg h]
      have he : ∃ i, s i ≠ t i := by
        by_contra hh
        push Not at hh
        exact h (funext hh)
      obtain ⟨i,hi⟩ := he
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  have tensorOp_update {N : ℕ} (w : Fin N → Local) (i : Fin N) (m : Local) (s t : Assignment N) : tensorProduct (Function.update w i m) s t = m (s i) (t i) * ∏ k ∈ Finset.univ.erase i, w k (s k) (t k) := by
    classical
    simp only [tensorOp_entries]; rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]; rw [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    rw [Function.update_of_ne (Finset.mem_erase.mp hk).1]
  have tensorOp_update_add {N : ℕ} (w : Fin N → Local) (i : Fin N) (u v : Local) : tensorProduct (Function.update w i (u + v)) = tensorProduct (Function.update w i u) + tensorProduct (Function.update w i v) := by
    classical
    ext s t
    simp only [tensorOp_update, Matrix.add_apply]; ring
  have fullNumber_eq_occupation {N : ℕ} (i : Fin N) : ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp i (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) = fullOccupationAt N i.val := by
    classical
    have h1 : numberWord i = Function.update (fun _ : Fin N => (1 : Local)) i (1-spinP) := by
      funext k
      simp [numberWord,Function.update]
    have h2 : (fun k : Fin N => if k.val=i.val then spinP else 1) = Function.update (fun _ : Fin N => (1 : Local)) i spinP := by
      funext k
      simp [Function.update,Fin.ext_iff]
    have he : ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp i (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) + fullPAt N i.val = 1 := by rw [localOp_as_tensor]; unfold fullPAt; rw [h1,h2,← tensorOp_update_add,sub_add_cancel]; rw [Function.update_eq_self_iff.mpr rfl,tensorOp_one]
    unfold fullOccupationAt; exact eq_sub_of_add_eq he
  have fullLeftP_eq (N j : ℕ) : fullLeftP N j = if j=0 then 1 else fullPAt N (j-1) := by
    classical
    by_cases hj : j=0
    · subst j
      change tensorProduct (fun k : Fin N => if k.val + 1 = 0 then spinP else 1) = 1
      have he : (fun k : Fin N => if k.val + 1 = 0 then spinP else (1 : Local)) = fun _ => 1 := by
        funext k
        simp
      rw [he,tensorOp_one]
    · rw [if_neg hj]
      unfold fullLeftP fullPAt
      congr 1
      funext k
      have he : k.val+1=j ↔ k.val=j-1 := by omega
      simp only [he]
  have fullPAt_eq_complement (N j : ℕ) : fullPAt N j = 1-fullOccupationAt N j := by
    unfold fullOccupationAt
    abel
  have chainG_periodic (a b cc : ℝ) (j : ℕ) : chainG a b cc (j+3) = chainG a b cc j := by unfold chainG; rw [show j+3+1=(j+1)+3 by omega,periodThree_periodic]
  have chainG_product (a b cc : ℝ) (j : ℕ) : chainG a b cc j * chainG a b cc (j+1) * chainG a b cc (j+2) = a*b*cc := by
    have hm : j%3=0 ∨ j%3=1 ∨ j%3=2 := by omega
    rcases hm with hm | hm | hm <;>
      norm_num [chainG,periodThree,Nat.add_mod,hm] <;> ring
  have chainG_previous (a b cc : ℝ) (j : ℕ) (hj : 0<j) : chainG a b cc (j-1) = chainG a b cc (j+2) := by
    have hp := chainG_periodic a b cc (j-1)
    rw [show j-1+3=j+2 by omega] at hp; exact hp.symm
  have fullQ_block_symmetric {N : ℕ} (a b cc : ℝ) (k : Fin N) (hr : k.val+2<N) : symOp (((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)) (D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion.antiAd ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm (fullQ (fun i : Fin N => chainG a b cc i.val))) ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm (blockR a b cc k hr))))) = blockDiagonal a b cc k hr + ((a*b*cc : ℝ) : ℂ) • (bulkCurrent N a b cc k.val + (if k.val=0 then 0 else fourCurrent N a b cc (k.val-1)) - fourCurrent N a b cc k.val) := by
    classical
    let g := chainG a b cc
    unfold blockR
    rw [antiOp_add,antiOp_smul,symOp_add,symOp_real_smul,
      fullQ_pair_symmetric_explicit g k hr,fullQ_split_symmetric g k hr]
    unfold blockDiagonal bulkCurrent hopCurrent fourCurrent
    simp only [fullNumber_eq_occupation,fullLeftP_eq,fullPAt_eq_complement,
      Matrix.smul_mul,smul_add,smul_sub,smul_smul]
    have hp : g (k.val+3)=g k.val := chainG_periodic a b cc k.val
    have hp1 : g (k.val+1+3)=g (k.val+1) := chainG_periodic a b cc (k.val+1)
    have ht : g k.val * g (k.val+1) * g (k.val+2) = a*b*cc := chainG_product a b cc k.val
    have hc : g (k.val+2) * g (k.val+1)^2 * g (k.val+3) = a*b*cc*g (k.val+1) := by
      calc
        g (k.val+2) * g (k.val+1)^2 * g (k.val+3) =
            (g k.val * g (k.val+1) * g (k.val+2)) * g (k.val+1) := by rw [hp]; ring
        _ = a*b*cc*g (k.val+1) := by rw [ht]
    by_cases hk : k.val=0
    · have hz : ¬0<k.val := by omega
      simp only [g,hk,hz,if_true,if_false,zero_mul,mul_zero,sub_zero,add_zero] at *; norm_num [chainG,periodThree,Nat.add_mod] at *
      try simp only [Matrix.smul_mul,smul_add,smul_sub,smul_smul]
      push_cast; module
    · have hk0 : 0<k.val := by omega
      have hm : g (k.val-1)=g (k.val+2) := chainG_previous a b cc k.val hk0
      have hcm : g k.val * g (k.val+1)^2 * g (k.val-1) = a*b*cc*g (k.val+1) := by
        calc
          g k.val * g (k.val+1)^2 * g (k.val-1) =
              (g k.val * g (k.val+1) * g (k.val+2)) * g (k.val+1) := by rw [hm]; ring
          _ = a*b*cc*g (k.val+1) := by rw [ht]
      simp only [g] at *; simp only [if_neg hk,if_pos hk0]
      simp only [show k.val+1+2=k.val+3 by omega,
        show k.val+2+2=(k.val+1)+3 by omega,
        show k.val-1+2=k.val+1 by omega,
        show k.val-1+3=k.val+2 by omega]
      simp only [chainG_periodic,hm] at hc hcm ⊢; rw [hc,hcm]
      try simp only [Matrix.smul_mul,smul_add,smul_sub,smul_smul]
      push_cast; module
  have fullOccupationAt_outside (N j : ℕ) (hj : N≤j) : fullOccupationAt N j = 0 := by
    have he : (fun k : Fin N => if k.val=j then spinP else (1 : Local)) = fun _ => 1 := by
      funext k
      have hn : k.val ≠ j := by omega
      simp [hn]
    change (1 : FullOperator N) - tensorProduct (fun k : Fin N => if k.val = j then spinP else 1) = 0
    rw [he,tensorOp_one,sub_self]
  have offDiagonal_bulk_telescope {α : Type} [Ring α] (k : ℕ) (C x : ℕ → α) (hC : C (k+1) = 0) (hx : x (k+2) = 0) : (∑ j ∈ Finset.range k, (C (j+1) * (1 - (if j=0 then 0 else x (j-1))) - C j * (1 - x (j+3)) + C (j+2) * x j - (if j=0 then 0 else C (j-1)) * x (j+2))) = C k - C 0 := by
    classical
    let F := fun j => C (j+1) * (if j=0 then 0 else x (j-1))
    let G := fun j => (if j=0 then 0 else C (j-1)) * x (j+2)
    have he (j : ℕ) : C (j+1) * (1 - (if j=0 then 0 else x (j-1))) - C j * (1 - x (j+3)) + C (j+2) * x j - (if j=0 then 0 else C (j-1)) * x (j+2) = (C (j+1) - C j) + (F (j+1) - F j) + (G (j+1) - G j) := by
      dsimp [F,G]
      rw [show j+1+1=j+2 by omega,show j+1+2=j+3 by omega]
      noncomm_ring
    simp only [he,Finset.sum_add_distrib,Finset.sum_range_sub]
    have hFk : F k = 0 := by dsimp [F]; rw [hC]; simp
    have hGk : G k = 0 := by dsimp [G]; rw [hx]; simp
    rw [hFk,hGk]; simp [F,G]
  have bulkCurrent_sum (N : ℕ) (hN : 3≤N) (a b cc : ℝ) : (∑ k : Fin (N-2), bulkCurrent N a b cc k.val) = hopCurrent N a b cc (N-2) - hopCurrent N a b cc 0 := by
    rw [Fin.sum_univ_eq_sum_range]; unfold bulkCurrent
    apply offDiagonal_bulk_telescope
    · unfold hopCurrent
      have hh : ¬N-2+1+1<N := by omega
      simp [fullHop,hh,symOp]
    · exact fullOccupationAt_outside N (N-2+2) (by omega)
  have predecessor_telescope {α : Type} [AddCommGroup α] (f : ℕ → α) (k : ℕ) : (∑ j ∈ Finset.range (k+1), ((if j=0 then 0 else f (j-1)) - f j)) = -f k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ,ih]; simp only [Nat.add_eq_zero_iff,one_ne_zero,and_false,if_false,Nat.add_sub_cancel]
      abel
  have fourCurrent_sum (N : ℕ) (hN : 3≤N) (a b cc : ℝ) : (∑ k : Fin (N-2), ((if k.val=0 then 0 else fourCurrent N a b cc (k.val-1)) - fourCurrent N a b cc k.val)) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun j =>
        ((if j=0 then 0 else fourCurrent N a b cc (j-1)) - fourCurrent N a b cc j)) (N-2),
      show N-2=(N-3)+1 by omega,predecessor_telescope]
    unfold fourCurrent
    have hh : ¬N-3+3<N := by omega
    simp [fullFourHop,hh,symOp]
  have fullQ_blocks_symmetric (N : ℕ) (hN : 3≤N) (a b cc : ℝ) : symOp (((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)) (D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion.antiAd ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm (fullQ (fun i : Fin N => chainG a b cc i.val))) ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm (∑ k : Fin (N-2), blockR a b cc (⟨k.val,by omega⟩ : Fin N) (by dsimp; omega)))))) = (∑ k : Fin (N-2), blockDiagonal a b cc (⟨k.val,by omega⟩ : Fin N) (by dsimp; omega)) + ((a*b*cc : ℝ) : ℂ) • (hopCurrent N a b cc (N-2) - hopCurrent N a b cc 0) := by
    classical
    rw [antiOp_sum,symOp_sum]; simp only [fullQ_block_symmetric,Finset.sum_add_distrib,← Finset.smul_sum]
    have he : (∑ k : Fin (N-2), (bulkCurrent N a b cc k.val + (if k.val=0 then 0 else fourCurrent N a b cc (k.val-1)) - fourCurrent N a b cc k.val)) = ∑ k : Fin (N-2), bulkCurrent N a b cc k.val := by
      have hm (k : Fin (N-2)) : bulkCurrent N a b cc k.val + (if k.val=0 then 0 else fourCurrent N a b cc (k.val-1)) - fourCurrent N a b cc k.val = bulkCurrent N a b cc k.val + ((if k.val=0 then 0 else fourCurrent N a b cc (k.val-1)) - fourCurrent N a b cc k.val) := by abel
      simp only [hm,Finset.sum_add_distrib,fourCurrent_sum N hN,add_zero]
    rw [he,bulkCurrent_sum N hN]
  have neighbourP_explicit {N : ℕ} (j : Fin N) : tensorProduct (neighbourPWord j) = fullLeftP N j.val * fullPAt N (j.val+1) := by
    unfold fullLeftP fullPAt; rw [tensorOp_mul]
    congr 1
    funext k
    unfold neighbourPWord
    by_cases hl : k.val+1=j.val
    · have hr : ¬k.val=j.val+1 := by omega
      simp only [if_pos (Or.inl hl),if_pos hl,if_neg hr,mul_one]
    · by_cases hr : k.val=j.val+1
      · simp only [if_pos (Or.inr hr),if_neg hl,if_pos hr,one_mul]
      · simp only [if_neg (not_or.mpr ⟨hl,hr⟩),if_neg hl,if_neg hr,one_mul]
  have creatorNeighbours_explicit {N : ℕ} (g : ℕ → ℝ) (j : Fin N) : creatorNeighbourTerms (fun i : Fin N => g i.val) j = (if 0<j.val then (g (j.val-1) : ℂ) • (fullHop N (j.val-1))ᴴ else 0) + (g (j.val+1) : ℂ) • fullHop N j.val := by
    classical
    have ht (i : Fin N) : (if i.val+1=j.val ∨ j.val+1=i.val then (g i.val : ℂ) • ((fullD j)ᴴ * fullD i) else 0) = (if i.val+1=j.val then (g i.val : ℂ) • ((fullD j)ᴴ * fullD i) else 0) + (if i.val=j.val+1 then (g i.val : ℂ) • ((fullD j)ᴴ * fullD i) else 0) := by
      have he : j.val+1=i.val ↔ i.val=j.val+1 := eq_comm
      simp only [he]
      by_cases hl : i.val+1=j.val
      · have hr : ¬i.val=j.val+1 := by omega
        simp only [if_pos (Or.inl hl),if_pos hl,if_neg hr,add_zero]
      · by_cases hr : i.val=j.val+1
        · simp only [if_pos (Or.inr hr),if_neg hl,if_pos hr,zero_add]
        · simp only [if_neg (not_or.mpr ⟨hl,hr⟩),if_neg hl,if_neg hr,add_zero]
    unfold creatorNeighbourTerms; simp_rw [ht]; rw [Finset.sum_add_distrib,sum_fin_before,sum_fin_at]
    congr 1
    · by_cases hl : 0<j.val
      · rw [dif_pos hl,if_pos hl]
        let i : Fin N := ⟨j.val-1,by omega⟩
        have hi : i.val+1<N := by dsimp [i]; omega
        have hij : (⟨i.val+1,hi⟩ : Fin N) = j := Fin.ext (by dsimp [i]; omega)
        have he : (fullD j)ᴴ * fullD i = (fullHop N (j.val-1))ᴴ := by
          change (fullD j)ᴴ * fullD i = (fullHop N i.val)ᴴ
          rw [hop_dressed i hi,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hij]
        exact congrArg (fun A : FullOperator N => (g (j.val-1) : ℂ) • A) he
      · rw [dif_neg hl,if_neg hl]
    · by_cases hr : j.val+1<N
      · rw [dif_pos hr,hop_dressed j hr]
      · simp [hr,fullHop]
  have symOp_neighbourP {N : ℕ} (j : Fin N) : symOp (tensorProduct (neighbourPWord j)) = (2 : ℂ) • tensorProduct (neighbourPWord j) := by
    have he : (tensorProduct (neighbourPWord j))ᴴ = tensorProduct (neighbourPWord j) := by
      rw [tensorOp_adjoint]
      congr 1
      funext k
      unfold neighbourPWord
      split_ifs <;> simp [spinP_self_adjoint]
    rw [symOp,he,two_smul ℂ _]
  have fullQ_creator_symmetric {N : ℕ} (g : ℕ → ℝ) (j : Fin N) : symOp (((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)) (D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion.antiAd ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm (fullQ (fun i : Fin N => g i.val))) ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm (fullD j)ᴴ)))) = ((2 * g j.val : ℝ) : ℂ) • tensorProduct (neighbourPWord j) + (if 0<j.val then (g (j.val-1) : ℂ) • symOp (fullHop N (j.val-1)) else 0) + (g (j.val+1) : ℂ) • symOp (fullHop N j.val) := by
    rw [antiAd_reindexed,fullQ_dressed_creator]
    change symOp ((g j.val : ℂ) • tensorProduct (neighbourPWord j) +
      creatorNeighbourTerms (fun i : Fin N => g i.val) j) = _
    rw [creatorNeighbours_explicit]; simp only [symOp_add,symOp_real_smul,symOp_neighbourP,smul_smul]
    have hz : symOp (0 : FullOperator N) = 0 := by simp [symOp]
    by_cases hh : 0<j.val <;> simp only [hh,if_pos,if_neg,ite_true,ite_false,symOp_real_smul,symOp_adjoint,hz,smul_smul,zero_add,add_zero]
    all_goals push_cast
    all_goals module
  have fullPAt_outside (N j : ℕ) (hj : N≤j) : fullPAt N j = 1 := by rw [fullPAt_eq_complement,fullOccupationAt_outside N j hj]; simp
  have fullBoundary_symmetric (N : ℕ) (hN : 3≤N) (hm : N%3=0) (a b cc : ℝ) : symOp (((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)) (D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion.antiAd ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm (fullQ (fun i : Fin N => chainG a b cc i.val))) ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm (fullBoundary N a b cc))))) = ((2*a^2*cc^2 : ℝ) : ℂ) • (fullPAt N 1 - fullPAt N (N-2)) + ((a*b*cc : ℝ) : ℂ) • (hopCurrent N a b cc 0 - hopCurrent N a b cc (N-2)) := by
    classical
    have hpos : 0<N := by omega
    let z : Fin N := ⟨0,hpos⟩
    let t : Fin N := ⟨N-1,by omega⟩
    have hz : tensorProduct (neighbourPWord z) = fullPAt N 1 := by rw [neighbourP_explicit,fullLeftP_eq]; simp [z]
    have ht : tensorProduct (neighbourPWord t) = fullPAt N (N-2) := by
      rw [neighbourP_explicit,fullLeftP_eq]
      have h0 : ¬t.val=0 := by dsimp [t]; omega
      have h1 : t.val+1=N := by dsimp [t]; omega
      have h2 : t.val-1=N-2 := by dsimp [t]; omega
      rw [if_neg h0,h1,h2,fullPAt_outside N N (le_refl N),mul_one]
    have hhop : fullHop N t.val = 0 := by
      have hh : ¬t.val+1<N := by dsimp [t]; omega
      simp [fullHop,hh]
    have hg0 : chainG a b cc 0 = a := by norm_num [chainG,periodThree]
    have hg1 : chainG a b cc 1 = b := by norm_num [chainG,periodThree]
    have hg2 : chainG a b cc 2 = cc := by norm_num [chainG,periodThree]
    have hgl : chainG a b cc t.val = cc := by unfold chainG; rw [show t.val+1=N by dsimp [t]; omega]; simp [periodThree,hm]
    have hgb : chainG a b cc (t.val-1) = b := by
      unfold chainG
      have h2 : t.val-1+1=N-1 := by dsimp [t]; omega
      have hmod : (N-1)%3=2 := by omega
      rw [h2]; simp [periodThree,hmod]
    have hgc : chainG a b cc (N-2+2) = a := by unfold chainG; rw [show N-2+2+1=N+1 by omega]; simp [periodThree,Nat.add_mod,hm]
    unfold fullBoundary; rw [dif_pos hpos,antiOp_sub,antiOp_smul,antiOp_smul,symOp_sub,symOp_real_smul,symOp_real_smul]
    rw [fullQ_creator_symmetric (chainG a b cc) z,
      fullQ_creator_symmetric (chainG a b cc) t,hz,ht,hgl,hgb,hhop]
    have h0 : ¬0<z.val := by dsimp [z]; omega
    have h1 : 0<t.val := by dsimp [t]; omega
    rw [if_neg h0,if_pos h1]
    have hs0 : symOp (0 : FullOperator N)=0 := by simp [symOp]
    simp only [hs0,smul_zero,zero_add,add_zero]; unfold hopCurrent; rw [hgc,hg2]; simp only [z,t,hg0,hg1,show N-1-1=N-2 by omega]; simp only [smul_add,smul_sub,smul_smul]; push_cast; module
  have full_symmetrized_diagonal (N : ℕ) (hN : 3≤N) (hm : N%3=0) (a b cc : ℝ) : symOp (((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)) (D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion.antiAd ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm (fullQ (fun i : Fin N => chainG a b cc i.val))) ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm (fullR N a b cc))))) = ((2*a^2*cc^2 : ℝ) : ℂ) • (fullPAt N 1 - fullPAt N (N-2)) + ∑ k : Fin (N-2), blockDiagonal a b cc (⟨k.val,by omega⟩ : Fin N) (by dsimp; omega) := by
    rw [fullR_blocks N (by omega),antiOp_add,symOp_add,
      fullBoundary_symmetric N hN hm,fullQ_blocks_symmetric N hN]
    module
  exact full_symmetrized_diagonal N hN hm a b cc
end
end D5.S3.Quantum.SpinChains.SupersymmetricFermion.FullEndpointIdentity
