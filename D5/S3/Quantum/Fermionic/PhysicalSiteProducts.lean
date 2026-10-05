/- GID: D5/S3/Quantum/Fermionic/PhysicalSiteProducts
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/PhysicalSiteProducts
   mirror-E: none(waiver:general-parity-and-products)
   anchors: []
   utility: none
   digest: Tensor site densities and their actual partial traces obey local number parity. -/

/-
one_site_marginal_physical:
  proof_shape: content
  escape_witness: factor global occupation parity through the split-site equivalence;
    cancelling the complementary parity in each traced summand gives local physicality.
site_parity_majorana:
  proof_shape: content
  escape_witness: the support of the Jordan-Wigner occupation matrix changes just one
    bit; the site's finite parity product flips precisely when that bit is at the site.
physical_products_zero:
  proof_shape: content
  escape_witness: conjugating each inter-site term by its first site parity
    preserves a physical tensor density and reverses the term, cancelling its trace.
admission_basis: escape-witness
Same-delivery inlined content: CoordinateEdgeHamiltonian, and local declarations.
Direct frozen public dependencies after inlining same-delivery content:
  GID: D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition.DensityState
    statement_id: sha256:b8e1957ba4f81600248989dc21f0a107bcdd5ce2e68546c38b9164c4a09ac337
  GID: D5/S3/Quantum/FiniteDimensional.qubitZ
    statement_id: sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c
  GID: D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.occupationCount
    statement_id: sha256:97804cfc85a668f345a5b3e2421ba02e5e6203f36590508faccac8726341bc0a
  GID: D5/S3/Quantum/Information/CorrelatedGibbsEnergyIdentity.meanEnergy
    statement_id: sha256:9968a03e56960da489176141fea72cbed63e67cc32e2fe1378c92e3fed11906b
  GID: D5/S3/Quantum/Information/PartialTraceMutualInformation.marginalRight
    statement_id: sha256:bb5bad02426b231285a1d49fbc7f66f6f971cf3cd7ef3ee92fc2c21793f14ae7
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.FullOperator
    statement_id: sha256:d0e241c65c207456599a205d965adefde23f6764456a0c5a832a08a676fadfb3
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.Local
    statement_id: sha256:cea3034ad5d4c2d36ac899cc7964a23cdad5b9a52b0410ee01f4b03ffd41f349
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fermionWord
    statement_id: sha256:d1484b5db3ace7148c685690abf5667976f26043e824bad34ea4385d5015100d
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fullC
    statement_id: sha256:e5eb14acc0a2901b62190a83ed2543f27309f7f32708edd35fa0376362ebfe97
  GID: D5/S3/Quantum/Dynamics/ClauseHamiltonian.Assignment
    statement_id: sha256:186896178b3ea09d109f4546cae53a1b2c485c3990a05a1b88d8deaaae3e423f
computational_content.kind: none; the statements are uniform in the site and mode counts.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.Fermionic.CoordinateEdgeHamiltonian
import D5.S3.Quantum.Information.CorrelatedGibbsEnergyIdentity

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder CStarAlgebra
open PredictiveThermodynamic.Physical (Assignment)
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Divergence.GibbsVariationalIdentity
open D5.S3.Quantum.Information.PartialTraceMutualInformation


noncomputable section
namespace D5.S3.Quantum.Fermionic.PhysicalSiteProducts

def siteProduct (n m : ℕ) (states : Fin n → DensityState (Assignment m)) :
    DensityState (Assignment (n*m)) := by
  classical
  let e : Assignment (n*m) ≃ (Fin n → Assignment m) :=
    (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans
      (Equiv.curry (Fin n) (Fin m) Bool)
  let M : Matrix (Fin n → Assignment m) (Fin n → Assignment m) ℂ :=
    fun x y => ∏ v, (states v).val (x v) (y v)
  have hM : M.PosSemidef := by
    let B : Fin n → Matrix (Assignment m) (Assignment m) ℂ :=
      fun v => CFC.sqrt (CStarMatrix.ofMatrix.symm (states v).val)
    let T : Matrix (Fin n → Assignment m) (Fin n → Assignment m) ℂ :=
      fun x y => ∏ v, B v (x v) (y v)
    have hroot (v : Fin n) : B v * (B v)ᴴ =
          (CStarMatrix.ofMatrix.symm (states v).val) := by
      have hs : (B v)ᴴ = B v :=
        (CFC.sqrt_nonneg (CStarMatrix.ofMatrix.symm (states v).val)).isSelfAdjoint.star_eq
      rw [hs]
      exact CFC.sqrt_mul_sqrt_self (CStarMatrix.ofMatrix.symm (states v).val)
        (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (states v).property.1)
    have hfactor : T * Tᴴ = M := by
      ext x y
      change (∑ z : Fin n → Assignment m,
        (∏ v, B v (x v) (z v)) * star (∏ v, B v (y v) (z v))) =
        ∏ v, (states v).val (x v) (y v)
      simp_rw [star_prod, ← Finset.prod_mul_distrib]
      rw [(Fintype.prod_sum (fun (v : Fin n) (z : Assignment m) =>
        B v (x v) z * star (B v (y v) z))).symm]
      apply Finset.prod_congr rfl
      intro v _
      exact congrArg (fun K : Matrix (Assignment m) (Assignment m) ℂ => K (x v) (y v)) (hroot v)
    rw [← hfactor]
    exact Matrix.posSemidef_self_mul_conjTranspose T
  refine ⟨CStarMatrix.ofMatrix (M.submatrix e e), ?_, ?_⟩
  · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (hM.submatrix e).nonneg
  · change Matrix.trace (M.submatrix e e) = 1
    change (∑ x : Assignment (n*m), M (e x) (e x)) = 1
    rw [e.sum_comp (fun x => M x x)]
    change (∑ x : Fin n → Assignment m, ∏ v, (states v).val (x v) (x v)) = 1
    rw [(Fintype.prod_sum (fun (v : Fin n) (x : Assignment m) => (states v).val x x)).symm]
    have ht (v : Fin n) : (∑ x : Assignment m, (states v).val x x) = 1 :=
      (states v).property.2
    simp only [ht, Finset.prod_const_one]


def oneSiteMarginal (n m : ℕ) (v : Fin n)
    (rho : DensityState (Assignment (n*m))) : DensityState (Assignment m) := by
  classical
  let e : Assignment (n*m) ≃ (Assignment m × ({w : Fin n // w ≠ v} → Assignment m)) :=
    ((Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans
      (Equiv.curry (Fin n) (Fin m) Bool)).trans (Equiv.funSplitAt v (Assignment m))
  let R := (CStarMatrix.ofMatrix.symm rho.val).submatrix e.symm e.symm
  have hR : R.PosSemidef :=
    (Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm rho.property.1)).submatrix e.symm
  have htr : Matrix.trace R = 1 := by
    change (∑ p, (CStarMatrix.ofMatrix.symm rho.val) (e.symm p) (e.symm p)) = 1
    rw [e.symm.sum_comp (fun x => (CStarMatrix.ofMatrix.symm rho.val) x x)]
    exact rho.property.2
  exact marginalRight ⟨CStarMatrix.ofMatrix R,
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hR.nonneg, htr⟩


open D5.S3.Quantum.Fermionic.FockMajoranaCarrier
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant (occupationCount)
open D5.S3.Quantum.Information.CorrelatedGibbsEnergyIdentity

def physicalState {n m : ℕ} (rho : DensityState (Assignment (n*m))) : Prop :=
  Commute rho.val (CStarMatrix.ofMatrix (numberParity (n*m)))

def physicalProduct {n m : ℕ} (rho : DensityState (Assignment (n*m))) : Prop :=
  ∃ states : Fin n → DensityState (Assignment m),
    (∀ v, Commute (states v).val (CStarMatrix.ofMatrix (numberParity m))) ∧
    rho = siteProduct n m states


end D5.S3.Quantum.Fermionic.PhysicalSiteProducts

namespace D5.S3.Quantum.Fermionic.PhysicalSiteProducts

open D5.S3.Quantum.Fermionic.FockMajoranaCarrier
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant (occupationCount)

/-- Global parity commutation descends to every actual one-site partial trace. -/
theorem one_site_marginal_physical (n m : ℕ) (v : Fin n) (rho : DensityState (Assignment (n*m)))
    (hphys : physicalState rho) :
    Commute (oneSiteMarginal n m v rho).val (CStarMatrix.ofMatrix (numberParity m)) := by
  classical
  have parity_diagonal (K : ℕ) : numberParity K = Matrix.diagonal
      (fun s => (-1 : ℂ) ^ (Finset.univ.filter (fun j => s j = true)).card) := by
    rw [numberParity_eq_diagonal]
    congr 1
    funext s
    congr 1
    unfold occupationCount
    have hbool (j : Fin K) : (s j).toNat = if s j = true then 1 else 0 := by
      cases s j <;> simp
    simp_rw [hbool]
    simp
  let e : Assignment (n*m) ≃ (Fin n → Assignment m) :=
    (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans
      (Equiv.curry (Fin n) (Fin m) Bool)
  let f := e.trans (Equiv.funSplitAt v (Assignment m))
  let sign (t : Assignment m) := (-1 : ℂ) ^ (Finset.univ.filter (fun j => t j = true)).card
  have hsign (t : Assignment m) : sign t = ∏ j : Fin m, if t j then (-1 : ℂ) else 1 := by
    dsimp [sign]
    rw [← Finset.prod_filter]
    simp [Finset.prod_const]
  have hglobal (t : Assignment (n*m)) :
      numberParity (n*m) t t = ∏ w : Fin n, sign (e t w) := by
    simp only [parity_diagonal, Matrix.diagonal_apply_eq]
    have hg : (-1 : ℂ) ^ (Finset.univ.filter (fun j => t j = true)).card =
        ∏ j : Fin (n*m), if t j then (-1 : ℂ) else 1 := by
      rw [← Finset.prod_filter]
      simp [Finset.prod_const]
    rw [hg]
    simp_rw [hsign]
    calc
      _ = ∏ p : Fin n × Fin m, if t (finProdFinEquiv p) then (-1 : ℂ) else 1 :=
        by
          simpa only [Equiv.apply_symm_apply] using Fintype.prod_equiv finProdFinEquiv.symm
            (fun j : Fin (n*m) => if t j then (-1 : ℂ) else 1)
            (fun p : Fin n × Fin m => if t (finProdFinEquiv p) then (-1 : ℂ) else 1)
            (fun j => by rw [Equiv.apply_symm_apply])
      _ = _ := by rw [Fintype.prod_prod_type]; rfl
  let restSign (t : {w : Fin n // w ≠ v} → Assignment m) := ∏ w, sign (t w)
  have hsplit (x : Assignment m) (b : {w : Fin n // w ≠ v} → Assignment m) :
      numberParity (n*m) (f.symm (x,b)) (f.symm (x,b)) = sign x * restSign b := by
    rw [hglobal, Fintype.prod_eq_mul_prod_subtype_ne _ v]
    have hx : e (f.symm (x,b)) v = x := by simp [f, Equiv.funSplitAt]
    have hb (w : {w : Fin n // w ≠ v}) : e (f.symm (x,b)) w.val = b w := by
      simp [f, Equiv.funSplitAt, w.property]
    simp only [hx, hb]
    rfl
  have hrest (b : {w : Fin n // w ≠ v} → Assignment m) : restSign b ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro w _
    exact pow_ne_zero _ (by norm_num)
  have hentry (x y : Assignment m) (b : {w : Fin n // w ≠ v} → Assignment m) :
      rho.val (f.symm (x,b)) (f.symm (y,b)) * sign y =
        sign x * rho.val (f.symm (x,b)) (f.symm (y,b)) := by
    have h := congrArg (fun A : CStarMatrix (Assignment (n*m)) (Assignment (n*m)) ℂ =>
      A (f.symm (x,b)) (f.symm (y,b))) hphys.eq
    change (CStarMatrix.ofMatrix.symm rho.val * numberParity (n*m)) _ _ =
      (numberParity (n*m) * CStarMatrix.ofMatrix.symm rho.val) _ _ at h
    simp only [parity_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    have hdiag (s : Assignment (n*m)) :
        (-1 : ℂ) ^ (Finset.univ.filter (fun j => s j = true)).card =
        numberParity (n*m) s s := by simp [parity_diagonal]
    simp only [hdiag] at h
    rw [hsplit,hsplit] at h
    exact (mul_right_cancel₀ (hrest b)) (by calc
      _ = rho.val (f.symm (x,b)) (f.symm (y,b)) * (sign y * restSign b) := by ring
      _ = (sign x * restSign b) * rho.val (f.symm (x,b)) (f.symm (y,b)) := h
      _ = _ := by ring)
  rw [commute_iff_eq]
  apply CStarMatrix.ext
  intro x y
  change (CStarMatrix.ofMatrix.symm (oneSiteMarginal n m v rho).val * numberParity m) x y =
    (numberParity m * CStarMatrix.ofMatrix.symm (oneSiteMarginal n m v rho).val) x y
  simp only [parity_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
  change (∑ b, rho.val (f.symm (x,b)) (f.symm (y,b))) * sign y =
    sign x * (∑ b, rho.val (f.symm (x,b)) (f.symm (y,b)))
  simp only [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun b _ => hentry x y b)

end D5.S3.Quantum.Fermionic.PhysicalSiteProducts

namespace D5.S3.Quantum.Fermionic.PhysicalSiteProducts

open D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner
open D5.S3.Quantum.Fermionic.FockMajoranaCarrier
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant (occupationCount)

def siteParity (n m : ℕ) (v : Fin n) : FullOperator (n*m) :=
  Matrix.diagonal (fun s => numberParity m (fun j => s (finProdFinEquiv (v,j)))
    (fun j => s (finProdFinEquiv (v,j))))

/-- The parity of one site flips precisely the Majoranas located at that site. -/
theorem site_parity_majorana (n m : ℕ) (v w : Fin n) (j : Fin m) (b : Bool) :
    (siteParity n m v).IsHermitian ∧ siteParity n m v * siteParity n m v = 1 ∧
    siteParity n m v * majorana (finProdFinEquiv (w,j)) b =
      (if v = w then (-1 : ℂ) else 1) •
        (majorana (finProdFinEquiv (w,j)) b * siteParity n m v) := by
  classical
  have parity_diagonal (K : ℕ) : numberParity K = Matrix.diagonal
      (fun s => (-1 : ℂ) ^ (Finset.univ.filter (fun j => s j = true)).card) := by
    rw [numberParity_eq_diagonal]
    congr 1
    funext s
    congr 1
    unfold occupationCount
    have hbool (j : Fin K) : (s j).toNat = if s j = true then 1 else 0 := by
      cases s j <;> simp
    simp_rw [hbool]
    simp
  let N := n*m
  let k := finProdFinEquiv (w,j)
  let sign (s : Assignment N) (l : Fin N) :=
    if (finProdFinEquiv.symm l).1 = v ∧ s l = true then (-1 : ℂ) else 1
  have hsign (s : Assignment N) :
      numberParity m (fun j => s (finProdFinEquiv (v,j)))
          (fun j => s (finProdFinEquiv (v,j))) = ∏ l : Fin N, sign s l := by
    simp only [parity_diagonal, Matrix.diagonal_apply_eq]
    have hp : (-1 : ℂ) ^ (Finset.univ.filter (fun j : Fin m =>
        s (finProdFinEquiv (v,j)) = true)).card =
        ∏ j : Fin m, if s (finProdFinEquiv (v,j)) then (-1 : ℂ) else 1 := by
      rw [← Finset.prod_filter]
      simp [Finset.prod_const]
    rw [hp]
    have he := Fintype.prod_equiv finProdFinEquiv
      (fun p : Fin n × Fin m => sign s (finProdFinEquiv p)) (sign s) (fun _ => rfl)
    rw [← he, Fintype.prod_prod_type]
    simp only [sign, Equiv.symm_apply_apply]
    simp_rw [ite_and, Finset.prod_ite_irrel]
    simp only [Finset.prod_const_one, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
  have hHerm : (siteParity n m v).IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro s
    rw [hsign]
    change star (∏ l : Fin N, sign s l) = _
    rw [star_prod]
    apply Finset.prod_congr rfl
    intro l _
    dsimp [sign]
    split_ifs <;> simp
  have hsquare : siteParity n m v * siteParity n m v = 1 := by
    rw [siteParity, Matrix.diagonal_mul_diagonal]
    have hs (s : Assignment N) : (∏ l : Fin N, sign s l) * (∏ l : Fin N, sign s l) = 1 := by
      rw [← Finset.prod_mul_distrib]
      have hl (l : Fin N) : sign s l * sign s l = 1 := by dsimp [sign]; split_ifs <;> norm_num
      simp only [hl, Finset.prod_const_one]
    simp only [hsign, hs, Matrix.diagonal_one]
  have hC : siteParity n m v * fullC k =
      (if v = w then (-1 : ℂ) else 1) • (fullC k * siteParity n m v) := by
    have entries (s t : Assignment N) : fullC k s t =
        ∏ l : Fin N, fermionWord k l (s l) (t l) := by
      simp [fullC, D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp,
        Matrix.submatrix_apply]
      rfl
    have off (l : Fin N) (hl : l ≠ k) (x y : Bool) (hxy : x ≠ y) :
        fermionWord k l x y = 0 := by
      by_cases hlt : l < k
      · cases x <;> cases y <;> simp_all [fermionWord,
          D5.S3.Quantum.FiniteDimensional.qubitZ, finTwoEquiv]
      · simp [fermionWord, hlt, hl, hxy]
    ext s t
    simp only [siteParity, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply,
      smul_eq_mul, hsign, entries]
    by_cases hrest : ∀ l, l ≠ k → s l = t l
    · have hp : (∏ l ∈ Finset.univ.erase k, sign s l) =
          (∏ l ∈ Finset.univ.erase k, sign t l) := by
        apply Finset.prod_congr rfl
        intro l hl
        simp only [sign, hrest l (Finset.ne_of_mem_erase hl)]
      rw [← Finset.mul_prod_erase Finset.univ (sign s) (Finset.mem_univ k),
        ← Finset.mul_prod_erase Finset.univ (sign t) (Finset.mem_univ k), hp]
      cases hs : s k <;> cases ht : t k
      · have hz : (∏ l : Fin N, fermionWord k l (s l) (t l)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ k) (by simp [fermionWord, hs, ht, Matrix.single])
        rw [hz]; simp
      · have hsp : sign s k = 1 := by dsimp only [sign]; rw [hs]; simp
        have htp : sign t k = (if v = w then (-1 : ℂ) else 1) := by
          dsimp only [sign]
          rw [ht]
          simp only [and_true]
          change (if (finProdFinEquiv.symm (finProdFinEquiv (w,j))).1 = v then _ else _) = _
          rw [Equiv.symm_apply_apply]
          simp only [eq_comm]
        rw [hsp,htp]
        split_ifs <;> ring
      · have hz : (∏ l : Fin N, fermionWord k l (s l) (t l)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ k) (by simp [fermionWord, hs, ht, Matrix.single])
        rw [hz]; simp
      · have hz : (∏ l : Fin N, fermionWord k l (s l) (t l)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ k) (by simp [fermionWord, hs, ht, Matrix.single])
        rw [hz]; simp
    · push Not at hrest
      obtain ⟨l,hl,hst⟩ := hrest
      have hz : (∏ l : Fin N, fermionWord k l (s l) (t l)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ l) (off l hl _ _ hst)
      rw [hz]; simp
  refine ⟨hHerm,hsquare,?_⟩
  have hd : siteParity n m v * (fullC k)ᴴ =
      (if v = w then (-1 : ℂ) else 1) • ((fullC k)ᴴ * siteParity n m v) := by
    have hh := congrArg Matrix.conjTranspose hC
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, hHerm.eq] at hh
    have hc : star (if v = w then (-1 : ℂ) else 1) = (if v = w then (-1 : ℂ) else 1) := by
      split_ifs <;> simp
    rw [hc] at hh
    by_cases hvw : v = w
    · simp only [hvw, ite_true, neg_one_smul] at hh ⊢
      exact eq_neg_of_add_eq_zero_left (by rw [hh]; simp)
    · simpa [hvw] using hh.symm
  cases b
  · change siteParity n m v * (fullC k + (fullC k)ᴴ) =
      (if v = w then (-1 : ℂ) else 1) • ((fullC k + (fullC k)ᴴ) * siteParity n m v)
    simp only [Matrix.mul_add, Matrix.add_mul, hC, hd, smul_add]
  · change siteParity n m v * (Complex.I • (fullC k - (fullC k)ᴴ)) =
      (if v = w then (-1 : ℂ) else 1) • ((Complex.I • (fullC k - (fullC k)ᴴ)) * siteParity n m v)
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, hC, hd, smul_sub]
    simp only [smul_comm (if v = w then (-1 : ℂ) else 1) Complex.I]

open D5.S3.Quantum.Information.CorrelatedGibbsEnergyIdentity
open D5.S3.Quantum.Fermionic.CoordinateEdgeHamiltonian

/-- Every physical site product has zero energy for the literal inter-site edge average. -/
theorem physical_products_zero {n m : ℕ} (G : SimpleGraph (Fin n))
    (K : G.edgeSet → Matrix (Fin m × Bool) (Fin m × Bool) ℝ)
    (rho : DensityState (Assignment (n*m))) (hrho : physicalProduct rho) :
    meanEnergy (averagedHamiltonian G K) rho = 0 := by
  classical
  have parity_diagonal (K : ℕ) : numberParity K = Matrix.diagonal
      (fun s => (-1 : ℂ) ^ (Finset.univ.filter (fun j => s j = true)).card) := by
    rw [numberParity_eq_diagonal]
    congr 1
    funext s
    congr 1
    unfold occupationCount
    have hbool (j : Fin K) : (s j).toNat = if s j = true then 1 else 0 := by
      cases s j <;> simp
    simp_rw [hbool]
    simp
  obtain ⟨states,hphys,rfl⟩ := hrho
  have hedge (v w : Fin n) (hvw : v ≠ w)
      (K : Matrix (Fin m × Bool) (Fin m × Bool) ℝ) :
      meanEnergy (quadraticEdge v w K) (siteProduct n m states) = 0 := by
    classical
    let P := siteParity n m v
    let M := CStarMatrix.ofMatrix.symm (siteProduct n m states).val
    let Q := CStarMatrix.ofMatrix.symm (quadraticEdge v w K)
    let e : Assignment (n*m) ≃ (Fin n → Assignment m) :=
      (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans
        (Equiv.curry (Fin n) (Fin m) Bool)
    let sign (s : Assignment m) := numberParity m s s
    have hPM : Commute P M := by
      rw [commute_iff_eq]
      ext x y
      simp only [P, siteParity, Matrix.diagonal_mul, Matrix.mul_diagonal]
      change sign (e x v) * (∏ u, (states u).val (e x u) (e y u)) =
        (∏ u, (states u).val (e x u) (e y u)) * sign (e y v)
      rw [Fintype.prod_eq_mul_prod_subtype_ne _ v]
      have hv := congrArg (fun A : CStarMatrix (Assignment m) (Assignment m) ℂ =>
        A (e x v) (e y v)) (hphys v).eq
      change (CStarMatrix.ofMatrix.symm (states v).val * numberParity m) _ _ =
        (numberParity m * CStarMatrix.ofMatrix.symm (states v).val) _ _ at hv
      simp only [parity_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul] at hv
      have hs (s : Assignment m) : (-1 : ℂ) ^ (Finset.univ.filter (fun j => s j = true)).card =
          sign s := by simp [sign, parity_diagonal]
      simp only [hs] at hv
      calc
        _ = (sign (e x v) * (states v).val (e x v) (e y v)) *
            (∏ u : {u : Fin n // u ≠ v}, (states u.val).val (e x u.val) (e y u.val)) := by ring
        _ = ((states v).val (e x v) (e y v) * sign (e y v)) *
            (∏ u : {u : Fin n // u ≠ v}, (states u.val).val (e x u.val) (e y u.val)) := by
          change (sign (e x v) * CStarMatrix.ofMatrix.symm (states v).val (e x v) (e y v)) * _ = _
          rw [← hv]
          rfl
        _ = _ := by ring
    have hsquare : P*P = 1 := by
      dsimp only [P]
      rw [siteParity, Matrix.diagonal_mul_diagonal]
      have hs (s : Assignment m) : numberParity m s s * numberParity m s s = 1 := by
        simp only [parity_diagonal, Matrix.diagonal_apply_eq, ← mul_pow]
        norm_num
      simp only [hs, Matrix.diagonal_one]
    have hodd (p q : Fin m × Bool) :
        P * (majorana (finProdFinEquiv (v,p.1)) p.2 * majorana (finProdFinEquiv (w,q.1)) q.2) =
        -(majorana (finProdFinEquiv (v,p.1)) p.2 * majorana (finProdFinEquiv (w,q.1)) q.2 * P) := by
      have hp := (site_parity_majorana n m v v p.1 p.2).2.2
      have hq := (site_parity_majorana n m v w q.1 q.2).2.2
      simp only [ite_true, neg_one_smul] at hp
      simp only [if_neg hvw, one_smul] at hq
      change P * majorana (finProdFinEquiv (v,p.1)) p.2 = _ at hp
      change P * majorana (finProdFinEquiv (w,q.1)) q.2 = _ at hq
      rw [← Matrix.mul_assoc,hp,Matrix.neg_mul,Matrix.mul_assoc,hq]
      simp only [Matrix.mul_assoc]
      rfl
    have hPQ : P*Q = -(Q*P) := by
      change P * (Complex.I • ∑ p : Fin m × Bool, ∑ q : Fin m × Bool,
        (K p q : ℂ) • (majorana (finProdFinEquiv (v,p.1)) p.2 *
          majorana (finProdFinEquiv (w,q.1)) q.2)) =
        -((Complex.I • ∑ p : Fin m × Bool, ∑ q : Fin m × Bool,
          (K p q : ℂ) • (majorana (finProdFinEquiv (v,p.1)) p.2 *
            majorana (finProdFinEquiv (w,q.1)) q.2)) * P)
      simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_sum,Matrix.sum_mul]
      simp_rw [hodd]
      simp only [smul_neg,Finset.sum_neg_distrib]
    have hinv : Matrix.trace (P*(Q*M)*P) = Matrix.trace (Q*M) := by
      rw [Matrix.trace_mul_cycle,← Matrix.mul_assoc,hsquare,Matrix.one_mul]
    have hneg : P*(Q*M)*P = -(Q*M) := by
      rw [← Matrix.mul_assoc,hPQ,Matrix.neg_mul,Matrix.mul_assoc,hPM.eq,
        Matrix.neg_mul,Matrix.mul_assoc,Matrix.mul_assoc,hsquare,Matrix.mul_one]
    rw [hneg,Matrix.trace_neg] at hinv
    have hz : Matrix.trace (Q*M) = 0 := by linear_combination -(1/2 : ℂ)*hinv
    change (Matrix.trace (Q*M)).re = 0
    rw [hz]
    rfl
  have hz (z : G.edgeSet) :
      meanEnergy (quadraticEdge z.val.out.1 z.val.out.2 (K z))
        (siteProduct n m states) = 0 := by
    have ha : G.Adj z.val.out.1 z.val.out.2 := by
      rw [← SimpleGraph.mem_edgeSet, Sym2.mk, z.val.out_eq]
      exact z.property
    exact hedge _ _ ha.ne _
  unfold averagedHamiltonian meanEnergy
  change (Matrix.trace (((G.edgeFinset.card : ℝ)⁻¹ •
    ∑ z : G.edgeSet, CStarMatrix.ofMatrix.symm
      (quadraticEdge z.val.out.1 z.val.out.2 (K z))) *
      CStarMatrix.ofMatrix.symm (siteProduct n m states).val)).re = 0
  simp only [Matrix.smul_mul, Matrix.sum_mul,
    Matrix.trace_smul, Matrix.trace_sum, Complex.smul_re, Complex.re_sum]
  change (G.edgeFinset.card : ℝ)⁻¹ *
    (∑ z : G.edgeSet, meanEnergy (quadraticEdge z.val.out.1 z.val.out.2 (K z))
      (siteProduct n m states)) = 0
  simp only [hz, Finset.sum_const_zero, mul_zero]

end D5.S3.Quantum.Fermionic.PhysicalSiteProducts
