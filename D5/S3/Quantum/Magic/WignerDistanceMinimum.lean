/- GID: D5/S3/Quantum/Magic/WignerDistanceMinimum
   generality: I
   mirror-B: D5/B/S3/Quantum/Magic/WignerDistanceMinimum
   mirror-E: none(waiver:explicit-compact-minimum-attainment)
   anchors: []
   utility: none
   digest: The Wigner free sets are compact nonempty convex hulls, and COne/CTwo attain the source minimum. -/
/-
proof_shape: COne_min: content; CTwo_min: content
escape_witness: finite_stab constructs an injection of stabilizer projectors into finitely many subgroups;
  spectral_stabilizer and spectral_product_stabilizer give nonempty free sets; compact convex hulls
  and continuous L1 images attain Metric.infDist.
admission_basis: escape-witness
Direct frozen dependencies: D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence;
  D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence;
  D5/S3/QuantumBounds/CHSHWitness (TwoQubitMatrix).
Information-escape registration is paused under CLAUDE.md §3.9.
-/
import D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence
import D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
import D5.S3.QuantumBounds.CHSHWitness
import Mathlib.Analysis.Convex.Topology
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
noncomputable section
namespace D5.S3.Quantum.Magic.WignerDistanceMinimum
open Matrix Complex
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence (pauliSet plab)
open D5.S3.QuantumBounds.CHSHWitness (TwoQubitMatrix)
open scoped Kronecker ComplexOrder

abbrev PhasePoint := Fin 2 × Fin 2
def phasePoint (a : PhasePoint) : QubitMatrix :=
  (1 / 2 : ℂ) • (1 + ((-1 : ℂ) ^ (a.2 : ℕ)) • pauliMatrix .X +
    ((-1 : ℂ) ^ ((a.1 : ℕ) + (a.2 : ℕ))) • pauliMatrix .Y +
    ((-1 : ℂ) ^ (a.1 : ℕ)) • pauliMatrix .Z)
def phasePointTwo (a : PhasePoint × PhasePoint) : TwoQubitMatrix :=
  phasePoint a.1 ⊗ₖ phasePoint a.2
def Wigner {ι α : Type*} [Fintype ι] (A : α → Matrix ι ι ℂ) (ρ : Matrix ι ι ℂ) : α → ℝ :=
  fun a => (ρ * A a).trace.re / Fintype.card ι
def WignerOne (ρ : QubitMatrix) : PhasePoint → ℝ := Wigner phasePoint ρ
def WignerTwo (ρ : TwoQubitMatrix) : PhasePoint × PhasePoint → ℝ :=
  Wigner phasePointTwo ρ
def pauliTwo : Set TwoQubitMatrix :=
  {P | ∃ c ∈ ({1, -1, Complex.I, -Complex.I} : Set ℂ), ∃ p q : Pauli,
    P = c • (pauliMatrix p ⊗ₖ pauliMatrix q)}
/-- A normalized pure state is the unique common +1 eigenray of an abelian Pauli subgroup
of order equal to the Hilbert-space dimension. The subgroup lives in the unitary group,
so its multiplication and inverse are genuine matrix multiplication and adjoint. -/
def Stab {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Set (Matrix ι ι ℂ)) : Set (Matrix ι ι ℂ) :=
  {ρ | ∃ (S : Subgroup (Matrix.unitaryGroup ι ℂ)) (ψ : ι → ℂ),
    (∀ g : S, (g.val.val : Matrix ι ι ℂ) ∈ P) ∧
    Nat.card S = Fintype.card ι ∧
    (∀ g h : S, g * h = h * g) ∧
    (∑ i, ‖ψ i‖ ^ 2) = 1 ∧
    (∀ v : ι → ℂ, (∀ g : S, (g.val.val : Matrix ι ι ℂ) *ᵥ v = v) ↔
      ∃ c : ℂ, v = c • ψ) ∧
    ρ = Matrix.vecMulVec ψ (star ψ)}
private def StabOne : Set QubitMatrix := Stab pauliSet
private def StabTwo : Set TwoQubitMatrix := Stab pauliTwo
def Wfree {ι α : Type*} [Fintype ι] [DecidableEq ι] (A : α → Matrix ι ι ℂ) (P : Set (Matrix ι ι ℂ)) : Set (α → ℝ) :=
  convexHull ℝ (Wigner A '' Stab P)
def COne (ρ : QubitMatrix) : ℝ := Metric.infDist (WithLp.toLp 1 (WignerOne ρ)) (WithLp.toLp 1 '' Wfree phasePoint pauliSet)
def CTwo (ρ : TwoQubitMatrix) : ℝ :=
  Metric.infDist (WithLp.toLp 1 (WignerTwo ρ)) (WithLp.toLp 1 '' Wfree phasePointTwo pauliTwo)
private def spectral (p : Pauli) (ε : Fin 2) : QubitMatrix :=
  (1/2 : ℂ) • (1 + ((-1 : ℂ) ^ (ε : ℕ)) • pauliMatrix p)
private def eigenVector (p : Pauli) (ε : Fin 2) : Fin 2 → ℂ :=
  let r : ℂ := ((Real.sqrt 2)⁻¹ : ℝ); let t : ℂ := (-1 : ℂ) ^ (ε : ℕ)
  match p with
  | .I => ![1,0]
  | .X => ![r,t*r]
  | .Y => ![r,Complex.I*t*r]
  | .Z => if ε = 0 then ![1,0] else ![0,1]
private theorem spectral_stabilizer (p : Pauli) (ε : Fin 2) (hp : p ≠ .I) : spectral p ε ∈ StabOne ∧ ∃ U : Multiplicative (ZMod 2) →* Matrix.unitaryGroup (Fin 2) ℂ, Function.Injective U ∧ (∀ x, (U x).val ∈ pauliSet) ∧ (∀ x, ((U x).val).trace = if x = 1 then 2 else 0) ∧ (∑ i, ‖eigenVector p ε i‖ ^ 2 = 1) ∧ ((Fintype.card (Multiplicative (ZMod 2)) : ℂ)⁻¹ • (∑ x, (U x).val) = Matrix.vecMulVec (eigenVector p ε) (star (eigenVector p ε))) ∧ spectral p ε = Matrix.vecMulVec (eigenVector p ε) (star (eigenVector p ε)) := by
  classical
  let P : QubitMatrix := ((-1 : ℂ) ^ (ε : ℕ)) • pauliMatrix p; have hPstar : star P = P := by
    cases p <;> fin_cases ε <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [P,pauliMatrix,qubitX,qubitZ,Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,Matrix.ofNat_apply,Complex.ext_iff]
  have hP2 : P*P = 1 := by
    cases p <;> fin_cases ε <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [P,pauliMatrix,qubitX,qubitZ,Matrix.mul_apply,Fin.sum_univ_two, Matrix.ofNat_apply,Complex.ext_iff]
  have hPne : P ≠ 1 := by
    cases p <;> try contradiction
    all_goals fin_cases ε <;> intro heq
    all_goals
      have he := congrArg (fun M : QubitMatrix => (M 0 0).re) heq; have he1 := congrArg (fun M : QubitMatrix => (M 1 1).re) heq
      try norm_num [P,pauliMatrix,qubitX,qubitZ,Matrix.ofNat_apply] at he
    all_goals norm_num [P,pauliMatrix,qubitX,qubitZ,Matrix.ofNat_apply] at he1
  have hm0 : Multiplicative.ofAdd (0 : ZMod 2) = 1 := rfl; have hm1 : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide
  have hsqtag : Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 := rfl; let U : Multiplicative (ZMod 2) →* Matrix.unitaryGroup (Fin 2) ℂ :=
    { toFun := fun x => ⟨if x = 1 then 1 else P,
        by split_ifs <;> rw [Matrix.mem_unitaryGroup_iff] <;> simp [hPstar,hP2]⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro x y; apply Subtype.ext; change (if x*y=1 then (1 : QubitMatrix) else P) =
          (if x=1 then (1 : QubitMatrix) else P)*(if y=1 then (1 : QubitMatrix) else P)
        fin_cases x <;> fin_cases y
        · change (if (1 : Multiplicative (ZMod 2))*1=1 then 1 else P) =
            (if (1 : Multiplicative (ZMod 2))=1 then 1 else P)*(if (1 : Multiplicative (ZMod 2))=1 then 1 else P)
          simp
        · change (if (1 : Multiplicative (ZMod 2))*Multiplicative.ofAdd (1 : ZMod 2)=1 then 1 else P) =
            (if (1 : Multiplicative (ZMod 2))=1 then 1 else P)*(if Multiplicative.ofAdd (1 : ZMod 2)=1 then 1 else P)
          simp only [one_mul,hm1,if_neg,if_pos,mul_one]
        · change (if Multiplicative.ofAdd (1 : ZMod 2)*(1 : Multiplicative (ZMod 2))=1 then 1 else P) =
            (if Multiplicative.ofAdd (1 : ZMod 2)=1 then 1 else P)*(if (1 : Multiplicative (ZMod 2))=1 then 1 else P)
          simp only [mul_one,hm1,if_neg,if_pos]
        · change (if Multiplicative.ofAdd (1 : ZMod 2)*Multiplicative.ofAdd (1 : ZMod 2)=1 then 1 else P) =
            (if Multiplicative.ofAdd (1 : ZMod 2)=1 then 1 else P)*(if Multiplicative.ofAdd (1 : ZMod 2)=1 then 1 else P)
          simp only [hsqtag,hm1,if_pos,if_neg,if_false,hP2]
    }
  have hU : Function.Injective U := by
    intro x y hh; have hm := congrArg Subtype.val hh
    fin_cases x <;> fin_cases y <;> try rfl
    all_goals simp [U,hm0,hm1] at hm
    · exact (hPne hm.symm).elim
    · exact (hPne hm).elim
  have hUP (x : Multiplicative (ZMod 2)) : (U x).val ∈ pauliSet := by
    fin_cases x
    · refine ⟨1,by simp,.I,?_⟩
      change (if (1 : Multiplicative (ZMod 2))=1 then (1 : QubitMatrix) else P) = 1 • pauliMatrix .I; simp [pauliMatrix]
    · refine ⟨(-1 : ℂ) ^ (ε : ℕ),?_,p,?_⟩
      · fin_cases ε <;> simp
      · change (if Multiplicative.ofAdd (1 : ZMod 2)=1 then (1 : QubitMatrix) else P) = _
        rw [if_neg hm1]
  have hcard : Fintype.card (Multiplicative (ZMod 2)) = Fintype.card (Fin 2) := by
    simp
  have hpsi : Matrix.vecMulVec (eigenVector p ε) (star (eigenVector p ε)) = spectral p ε := by
    have hr : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hn : Real.sqrt 2 ≠ 0 := by positivity
    have hrr : ((Real.sqrt 2)⁻¹ : ℝ) * (Real.sqrt 2)⁻¹ = 1/2 := by
      field_simp; nlinarith [hr]
    have hrrC : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * ((Real.sqrt 2)⁻¹ : ℝ) = 1/2 := by
      simpa only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using congrArg Complex.ofReal hrr
    cases p <;> try contradiction
    all_goals fin_cases ε <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [eigenVector,spectral,pauliMatrix,qubitX,qubitZ,Matrix.vecMulVec, Matrix.ofNat_apply,hrrC,Complex.mul_re,Complex.mul_im]
    all_goals
      apply Complex.ext <;> norm_num [Complex.mul_re,Complex.mul_im] <;> nlinarith [hrr]
  have hnorm : ∑ i, ‖eigenVector p ε i‖ ^ 2 = 1 := by
    have ht : (spectral p ε).trace = 1 := by
      cases p <;> try contradiction
      all_goals fin_cases ε <;> norm_num [spectral,pauliMatrix,qubitX,qubitZ,Matrix.trace]
    rw [← hpsi] at ht; have he : (Matrix.vecMulVec (eigenVector p ε) (star (eigenVector p ε))).trace = (∑ i, ‖eigenVector p ε i‖ ^ 2 : ℝ) := by
      simp [Matrix.trace,Matrix.vecMulVec,← Complex.normSq_eq_norm_sq,Complex.mul_conj]
    rw [he] at ht; exact_mod_cast ht
  have havg : (Fintype.card (Multiplicative (ZMod 2)) : ℂ)⁻¹ • (∑ g, (U g).val) = Matrix.vecMulVec (eigenVector p ε) (star (eigenVector p ε)) := by
    rw [hpsi]; have hsum : (∑ g, (U g).val) = 1+P := by
      change (∑ g : Multiplicative (ZMod 2), if g = 1 then (1 : QubitMatrix) else P) = _; have ht := Fintype.sum_equiv (Multiplicative.toAdd (α := ZMod 2))
        (fun x => if x=1 then (1 : QubitMatrix) else P)
        (fun i : ZMod 2 => if i = 0 then (1 : QubitMatrix) else P) (fun _ => rfl)
      rw [ht]; change (∑ i : Fin 2, if i = 0 then (1 : QubitMatrix) else P) = _; simp [Fin.sum_univ_two]
    rw [hsum]; norm_num [spectral,P]
  have htrace (x : Multiplicative (ZMod 2)) : ((U x).val).trace = if x = 1 then 2 else 0 := by
    fin_cases x
    · change (if (1 : Multiplicative (ZMod 2))=1 then (1 : QubitMatrix) else P).trace =
        if (1 : Multiplicative (ZMod 2))=1 then 2 else 0
      simp [Matrix.trace_one]
    · change (if Multiplicative.ofAdd (1 : ZMod 2)=1 then (1 : QubitMatrix) else P).trace =
        if Multiplicative.ofAdd (1 : ZMod 2)=1 then 2 else 0
      rw [if_neg hm1,if_neg hm1]
      cases p <;> try contradiction
      all_goals fin_cases ε <;> norm_num [P,pauliMatrix,qubitX,qubitZ,Matrix.trace]
  refine ⟨?_,U,hU,hUP,htrace,hnorm,havg,hpsi.symm⟩; rw [← hpsi]
  classical
  let S := U.range; have hn : (Fintype.card (Multiplicative (ZMod 2)) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have heigen (g : (Multiplicative (ZMod 2))) : (U g).val * Matrix.vecMulVec (eigenVector p ε) (star (eigenVector p ε)) = Matrix.vecMulVec (eigenVector p ε) (star (eigenVector p ε)) := by
    rw [← havg,Matrix.mul_smul,Finset.mul_sum]; simp only [← Submonoid.coe_mul,← U.map_mul]
    congr 1
    exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun h => rfl)
  have hproj : Matrix.vecMulVec (eigenVector p ε) (star (eigenVector p ε)) *ᵥ (eigenVector p ε) = (eigenVector p ε) := by
    have hdot : dotProduct (star (eigenVector p ε)) (eigenVector p ε) = 1 := by
      calc
        dotProduct (star (eigenVector p ε)) (eigenVector p ε) = (∑ i, (‖(eigenVector p ε) i‖ ^ 2 : ℝ) : ℂ) := by
          simp only [dotProduct,Pi.star_apply,Complex.star_def,← Complex.normSq_eq_conj_mul_self, Complex.ofReal_sum,Complex.ofReal_pow,Complex.normSq_eq_norm_sq]
        _ = 1 := by exact_mod_cast hnorm
    simp [Matrix.vecMulVec_mulVec,hdot]
  refine ⟨S,(eigenVector p ε),?_,?_,?_,hnorm,?_,rfl⟩
  · intro g
    obtain ⟨x,hx⟩ := g.property
    simpa [← hx] using hUP x
  · change Nat.card U.range = Fintype.card (Fin 2)
    change Nat.card (Set.range U) = Fintype.card (Fin 2)
    exact (Nat.card_congr (Equiv.ofInjective U hU)).symm.trans (by simp [hcard])
  · intro g h
    obtain ⟨x,hx⟩ := g.property; obtain ⟨y,hy⟩ := h.property; apply Subtype.ext; change g.val * h.val = h.val * g.val; rw [← hx,← hy,← U.map_mul,← U.map_mul]
    exact congrArg U (mul_comm x y)
  · intro v
    constructor
    · intro hv
      have hfixed (g : (Multiplicative (ZMod 2))) : (U g).val *ᵥ v = v := hv ⟨U g,⟨g,rfl⟩⟩; have hPv : Matrix.vecMulVec (eigenVector p ε) (star (eigenVector p ε)) *ᵥ v = v := by
        rw [← havg,Matrix.smul_mulVec,Matrix.sum_mulVec]; simp_rw [hfixed]; ext i; simp [hn]
      exact ⟨dotProduct (star (eigenVector p ε)) v, by simpa only [Matrix.vecMulVec_mulVec, op_smul_eq_smul] using hPv.symm⟩
    · rintro ⟨c,rfl⟩ g
      obtain ⟨x,hx⟩ := g.property; have hf : (U x).val *ᵥ (eigenVector p ε) = (eigenVector p ε) := by
        calc
          (U x).val *ᵥ (eigenVector p ε) = (U x).val *ᵥ (Matrix.vecMulVec (eigenVector p ε) (star (eigenVector p ε)) *ᵥ (eigenVector p ε)) := by rw [hproj]
          _ = (eigenVector p ε) := by rw [Matrix.mulVec_mulVec,heigen,hproj]
      simpa [← hx,Matrix.mulVec_smul,hf]
private theorem spectral_product_stabilizer (p q : Pauli) (ε δ : Fin 2) (hp : p ≠ .I) (hq : q ≠ .I) : spectral p ε ⊗ₖ spectral q δ ∈ StabTwo := by
  classical
  obtain ⟨_,U,hU,hUP,hUt,hψnorm,hUavg,hψ⟩ := spectral_stabilizer p ε hp; obtain ⟨_,V,hV,hVP,hVt,hφnorm,hVavg,hφ⟩ := spectral_stabilizer q δ hq; let G := Multiplicative (ZMod 2)
  let T : G × G →* Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ :=
    { toFun := fun x => ⟨(U x.1).val ⊗ₖ (V x.2).val,
        Matrix.kronecker_mem_unitary (U x.1).property (V x.2).property⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro x y; apply Subtype.ext; simp only [Prod.fst_mul,Prod.snd_mul,U.map_mul,V.map_mul,Submonoid.coe_mul]
        exact Matrix.mul_kronecker_mul _ _ _ _ }
  have hT : Function.Injective T := by
    have hk (x : G × G) (hx : T x = 1) : x = 1 := by
      have ht := congrArg (fun M : Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ => M.val.trace) hx; change ((U x.1).val ⊗ₖ (V x.2).val).trace = (1 : TwoQubitMatrix).trace at ht; rw [Matrix.trace_kronecker,hUt,hVt] at ht
      by_cases ha : x.1 = 1 <;> by_cases hb : x.2 = 1
      · exact Prod.ext ha hb
      all_goals norm_num [ha,hb,Matrix.trace_one] at ht
    intro x y hxy; have hker : T (x⁻¹*y) = 1 := by rw [T.map_mul,T.map_inv,hxy,inv_mul_cancel]
    have hz := hk (x⁻¹*y) hker
    exact inv_mul_eq_one.mp hz
  have hTP (x : G × G) : (T x).val ∈ pauliTwo := by
    rcases hUP x.1 with ⟨c,hc,p',hpc⟩; rcases hVP x.2 with ⟨d,hd,q',hqd⟩; refine ⟨c*d,?_,p',q',?_⟩
    · simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hc hd ⊢
      rcases hc with rfl | rfl | rfl | rfl <;>
        rcases hd with rfl | rfl | rfl | rfl <;> norm_num
    · change (U x.1).val ⊗ₖ (V x.2).val = _
      rw [hpc,hqd,Matrix.smul_kronecker,Matrix.kronecker_smul,smul_smul]
  let ψ : Fin 2 × Fin 2 → ℂ := fun i => eigenVector p ε i.1 * eigenVector q δ i.2; have hnorm : ∑ i, ‖ψ i‖ ^ 2 = 1 := by
    dsimp [ψ]; simp only [norm_mul,mul_pow]; rw [Fintype.sum_prod_type]; change (∑ x : Fin 2, ∑ y : Fin 2, ‖eigenVector p ε x‖ ^ 2 * ‖eigenVector q δ y‖ ^ 2) = 1; rw [← Fintype.sum_mul_sum,hψnorm,hφnorm]; norm_num
  have houter : Matrix.vecMulVec ψ (star ψ) = Matrix.vecMulVec (eigenVector p ε) (star (eigenVector p ε)) ⊗ₖ Matrix.vecMulVec (eigenVector q δ) (star (eigenVector q δ)) := by
    ext i j; simp [ψ,Matrix.vecMulVec,Matrix.kroneckerMap_apply,mul_comm,mul_left_comm,mul_assoc]
  have hcard : Fintype.card (G × G) = Fintype.card (Fin 2 × Fin 2) := by simp [G]
  have havg : (Fintype.card (G × G) : ℂ)⁻¹ • (∑ x, (T x).val) = Matrix.vecMulVec ψ (star ψ) := by
    rw [houter,← hUavg,← hVavg]; norm_num [G,Fintype.card_prod,Fintype.card_multiplicative,ZMod.card]; have hsum : (∑ x : G × G, (T x).val) = (∑ x : G, (U x).val) ⊗ₖ (∑ x : G, (V x).val) := by
      change (∑ x : G × G, (U x.1).val ⊗ₖ (V x.2).val) = _; rw [Fintype.sum_prod_type]; ext i j; simp only [Matrix.sum_apply,Matrix.kroneckerMap_apply]
      exact (Fintype.sum_mul_sum (fun x : G => (U x).val i.1 j.1)
        (fun x : G => (V x).val i.2 j.2)).symm
    rw [hsum,Matrix.smul_kronecker,Matrix.kronecker_smul,smul_smul]; norm_num
    rfl
  rw [hψ,hφ,← houter]
  classical
  let S := T.range; have hn : (Fintype.card (G × G) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have heigen (g : (G × G)) : (T g).val * Matrix.vecMulVec ψ (star ψ) = Matrix.vecMulVec ψ (star ψ) := by
    rw [← havg,Matrix.mul_smul,Finset.mul_sum]; simp only [← Submonoid.coe_mul,← T.map_mul]
    congr 1
    exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun h => rfl)
  have hproj : Matrix.vecMulVec ψ (star ψ) *ᵥ ψ = ψ := by
    have hdot : dotProduct (star ψ) ψ = 1 := by
      calc
        dotProduct (star ψ) ψ = (∑ i, (‖ψ i‖ ^ 2 : ℝ) : ℂ) := by
          simp only [dotProduct,Pi.star_apply,Complex.star_def,← Complex.normSq_eq_conj_mul_self, Complex.ofReal_sum,Complex.ofReal_pow,Complex.normSq_eq_norm_sq]
        _ = 1 := by exact_mod_cast hnorm
    simp [Matrix.vecMulVec_mulVec,hdot]
  refine ⟨S,ψ,?_,?_,?_,hnorm,?_,rfl⟩
  · intro g
    obtain ⟨x,hx⟩ := g.property
    simpa [← hx] using hTP x
  · change Nat.card T.range = Fintype.card (Fin 2 × Fin 2)
    change Nat.card (Set.range T) = Fintype.card (Fin 2 × Fin 2)
    exact (Nat.card_congr (Equiv.ofInjective T hT)).symm.trans (by simp [hcard])
  · intro g h
    obtain ⟨x,hx⟩ := g.property; obtain ⟨y,hy⟩ := h.property; apply Subtype.ext; change g.val * h.val = h.val * g.val; rw [← hx,← hy,← T.map_mul,← T.map_mul]
    exact congrArg T (mul_comm x y)
  · intro v
    constructor
    · intro hv
      have hfixed (g : (G × G)) : (T g).val *ᵥ v = v := hv ⟨T g,⟨g,rfl⟩⟩; have hPv : Matrix.vecMulVec ψ (star ψ) *ᵥ v = v := by
        rw [← havg,Matrix.smul_mulVec,Matrix.sum_mulVec]; simp_rw [hfixed]; ext i; simp [G]
      exact ⟨dotProduct (star ψ) v, by simpa only [Matrix.vecMulVec_mulVec, op_smul_eq_smul] using hPv.symm⟩
    · rintro ⟨c,rfl⟩ g
      obtain ⟨x,hx⟩ := g.property; have hf : (T x).val *ᵥ ψ = ψ := by
        calc
          (T x).val *ᵥ ψ = (T x).val *ᵥ (Matrix.vecMulVec ψ (star ψ) *ᵥ ψ) := by rw [hproj]
          _ = ψ := by rw [Matrix.mulVec_mulVec,heigen,hproj]
      simpa [← hx,Matrix.mulVec_smul,hf]
private theorem finite_stab {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Set (Matrix ι ι ℂ)) (hP : P.Finite) : (Stab P).Finite := by
  classical
  let U : Matrix.unitaryGroup ι ℂ → Matrix ι ι ℂ := fun g => g.val
  have hU : Function.Injective U := Subtype.val_injective
  let T : Set (Subgroup (Matrix.unitaryGroup ι ℂ)) := {S | (S : Set _) ⊆ U ⁻¹' P}
  have hsub : T.Finite :=
    ((hP.preimage hU.injOn).finite_subsets).preimage SetLike.coe_injective.injOn
  let pick : {ρ // ρ ∈ Stab P} → Subgroup (Matrix.unitaryGroup ι ℂ) :=
    fun ρ => Classical.choose ρ.property
  have hpick (ρ : {ρ // ρ ∈ Stab P}) : pick ρ ∈ T := by
    obtain ⟨ψ, hmem, hcard, hcomm, hnorm, hunique, heq⟩ := Classical.choose_spec ρ.property
    intro g hg
    exact hmem ⟨g, hg⟩
  have hinj : Function.Injective pick := by
    intro ρ σ heq
    obtain ⟨ψ, hmem, hcard, hcomm, hnorm, hunique, hr⟩ := Classical.choose_spec ρ.property
    obtain ⟨φ, hmem', hcard', hcomm', hnorm', hunique', hs⟩ := Classical.choose_spec σ.property
    change pick ρ = pick σ at heq
    have hu : ∀ v : ι → ℂ, (∀ g : pick ρ, (g.val.val : Matrix ι ι ℂ) *ᵥ v = v) ↔
      ∃ c : ℂ, v = c • φ := by rw [heq]; exact hunique'
    apply Subtype.ext
    rw [hr, hs]
    have normalized_projector_unique :
        Matrix.vecMulVec ψ (star ψ) = Matrix.vecMulVec φ (star φ) := by
      obtain ⟨c, hc⟩ := (hunique φ).mp ((hu φ).mpr ⟨1, by simp⟩)
      have hcnorm : ‖c‖ ^ 2 = 1 := by
        calc
          ‖c‖ ^ 2 = ‖c‖ ^ 2 * (∑ i, ‖ψ i‖ ^ 2) := by rw [hnorm, mul_one]
          _ = ∑ i, ‖c * ψ i‖ ^ 2 := by simp_rw [norm_mul, mul_pow]; rw [Finset.mul_sum]
          _ = 1 := by simpa [hc, Pi.smul_apply, smul_eq_mul] using hnorm'
      have hphase : c * star c = 1 := by
        simpa [Complex.mul_conj, Complex.normSq_eq_norm_sq, hcnorm]
      rw [hc]
      ext i j
      simp only [Matrix.vecMulVec, Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul]
      change ψ i * star (ψ j) = c * ψ i * (star (ψ j) * star c)
      calc
        ψ i * star (ψ j) = (c * star c) * (ψ i * star (ψ j)) := by rw [hphase, one_mul]
        _ = c * ψ i * (star (ψ j) * star c) := by ring
    exact normalized_projector_unique
  letI : Finite {S // S ∈ T} := hsub.to_subtype
  letI : Finite {ρ // ρ ∈ Stab P} := Finite.of_injective
    (fun ρ => (⟨pick ρ, hpick ρ⟩ : {S // S ∈ T}))
    (by intro ρ σ h; exact hinj (congrArg Subtype.val h))
  exact Set.toFinite _

theorem COne_min (ρ : QubitMatrix) :
    ∃ f ∈ Wfree phasePoint pauliSet,
      COne ρ = ‖WithLp.toLp 1 (WignerOne ρ - f)‖ ∧
        ∀ g ∈ Wfree phasePoint pauliSet,
          COne ρ ≤ ‖WithLp.toLp 1 (WignerOne ρ - g)‖ := by
  have hP : pauliSet.Finite := by
    have hp : ({1, -1, Complex.I, -Complex.I} : Set ℂ).Finite := by simp
    have h := hp.prod (Set.finite_univ : (Set.univ : Set Pauli).Finite)
    refine (h.image (fun cp : ℂ × Pauli => cp.1 • pauliMatrix cp.2)).subset ?_
    rintro A ⟨c, hc, p, rfl⟩
    exact ⟨(c,p), ⟨hc, Set.mem_univ _⟩, rfl⟩
  have hcompact : IsCompact (Wfree phasePoint pauliSet) :=
    ((finite_stab pauliSet hP).image (Wigner phasePoint)).isCompact_convexHull ℝ
  have hnonempty : (Wfree phasePoint pauliSet).Nonempty := by
    refine ⟨WignerOne (spectral .Z 0), ?_⟩
    apply subset_convexHull ℝ _
    exact ⟨spectral .Z 0, (spectral_stabilizer .Z 0 (by decide)).1, rfl⟩
  obtain ⟨y, ⟨f, hf, rfl⟩, hy⟩ :=
    (hcompact.image (PiLp.continuous_toLp 1 (fun _ : PhasePoint => ℝ))).exists_infDist_eq_dist
      (hnonempty.image (WithLp.toLp 1)) (WithLp.toLp 1 (WignerOne ρ))
  have hEq : COne ρ = ‖WithLp.toLp 1 (WignerOne ρ - f)‖ := by
    rw [COne]
    calc
      Metric.infDist (WithLp.toLp 1 (WignerOne ρ))
          (WithLp.toLp 1 '' Wfree phasePoint pauliSet) =
          dist (WithLp.toLp 1 (WignerOne ρ)) (WithLp.toLp 1 f) := hy
      _ = ‖WithLp.toLp 1 (WignerOne ρ - f)‖ := by
        simpa [dist_eq_norm, PiLp.norm_eq_of_L1, PiLp.toLp_apply,
          sub_eq_add_neg, add_comm]
  refine ⟨f, hf, hEq, ?_⟩
  intro g hg
  have hle : Metric.infDist (WithLp.toLp 1 (WignerOne ρ))
      (WithLp.toLp 1 '' Wfree phasePoint pauliSet) ≤
      dist (WithLp.toLp 1 (WignerOne ρ)) (WithLp.toLp 1 g) :=
    Metric.infDist_le_dist_of_mem (x := WithLp.toLp 1 (WignerOne ρ))
      (show WithLp.toLp 1 g ∈ WithLp.toLp 1 '' Wfree phasePoint pauliSet from ⟨g, hg, rfl⟩)
  calc
    COne ρ = Metric.infDist (WithLp.toLp 1 (WignerOne ρ))
        (WithLp.toLp 1 '' Wfree phasePoint pauliSet) := rfl
    _ ≤ dist (WithLp.toLp 1 (WignerOne ρ)) (WithLp.toLp 1 g) := hle
    _ = ‖WithLp.toLp 1 (WignerOne ρ - g)‖ := by
      simpa [dist_eq_norm, PiLp.norm_eq_of_L1, PiLp.toLp_apply,
        sub_eq_add_neg, add_comm]

theorem CTwo_min (ρ : TwoQubitMatrix) :
    ∃ f ∈ Wfree phasePointTwo pauliTwo,
      CTwo ρ = ‖WithLp.toLp 1 (WignerTwo ρ - f)‖ ∧
        ∀ g ∈ Wfree phasePointTwo pauliTwo,
          CTwo ρ ≤ ‖WithLp.toLp 1 (WignerTwo ρ - g)‖ := by
  have hP : pauliTwo.Finite := by
    have hp : ({1, -1, Complex.I, -Complex.I} : Set ℂ).Finite := by simp
    have h := hp.prod (Set.finite_univ : (Set.univ : Set (Pauli × Pauli)).Finite)
    refine (h.image (fun cp : ℂ × (Pauli × Pauli) =>
      cp.1 • (pauliMatrix cp.2.1 ⊗ₖ pauliMatrix cp.2.2))).subset ?_
    rintro A ⟨c, hc, p, q, rfl⟩
    exact ⟨(c,(p,q)), ⟨hc, Set.mem_univ _⟩, rfl⟩
  have hcompact : IsCompact (Wfree phasePointTwo pauliTwo) :=
    ((finite_stab pauliTwo hP).image (Wigner phasePointTwo)).isCompact_convexHull ℝ
  have hnonempty : (Wfree phasePointTwo pauliTwo).Nonempty := by
    refine ⟨WignerTwo (spectral .Z 0 ⊗ₖ spectral .Z 0), ?_⟩
    apply subset_convexHull ℝ _
    exact ⟨spectral .Z 0 ⊗ₖ spectral .Z 0,
      spectral_product_stabilizer .Z .Z 0 0 (by decide) (by decide), rfl⟩
  obtain ⟨y, ⟨f, hf, rfl⟩, hy⟩ :=
    (hcompact.image (PiLp.continuous_toLp 1 (fun _ : PhasePoint × PhasePoint => ℝ))).exists_infDist_eq_dist
      (hnonempty.image (WithLp.toLp 1)) (WithLp.toLp 1 (WignerTwo ρ))
  have hEq : CTwo ρ = ‖WithLp.toLp 1 (WignerTwo ρ - f)‖ := by
    rw [CTwo]
    calc
      Metric.infDist (WithLp.toLp 1 (WignerTwo ρ))
          (WithLp.toLp 1 '' Wfree phasePointTwo pauliTwo) =
          dist (WithLp.toLp 1 (WignerTwo ρ)) (WithLp.toLp 1 f) := hy
      _ = ‖WithLp.toLp 1 (WignerTwo ρ - f)‖ := by
        simpa [dist_eq_norm, PiLp.norm_eq_of_L1, PiLp.toLp_apply,
          sub_eq_add_neg, add_comm]
  refine ⟨f, hf, hEq, ?_⟩
  intro g hg
  have hle : Metric.infDist (WithLp.toLp 1 (WignerTwo ρ))
      (WithLp.toLp 1 '' Wfree phasePointTwo pauliTwo) ≤
      dist (WithLp.toLp 1 (WignerTwo ρ)) (WithLp.toLp 1 g) :=
    Metric.infDist_le_dist_of_mem (x := WithLp.toLp 1 (WignerTwo ρ))
      (show WithLp.toLp 1 g ∈ WithLp.toLp 1 '' Wfree phasePointTwo pauliTwo from ⟨g, hg, rfl⟩)
  calc
    CTwo ρ = Metric.infDist (WithLp.toLp 1 (WignerTwo ρ))
        (WithLp.toLp 1 '' Wfree phasePointTwo pauliTwo) := rfl
    _ ≤ dist (WithLp.toLp 1 (WignerTwo ρ)) (WithLp.toLp 1 g) := hle
    _ = ‖WithLp.toLp 1 (WignerTwo ρ - g)‖ := by
      simpa [dist_eq_norm, PiLp.norm_eq_of_L1, PiLp.toLp_apply,
        sub_eq_add_neg, add_comm]

end D5.S3.Quantum.Magic.WignerDistanceMinimum
