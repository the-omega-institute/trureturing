/- GID: D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules
   generality: I
   mirror-B: D5/B/S3/Quantum/Magic/QubitWignerDistanceTensorRules
   mirror-E: none(waiver:kernel-checked-universal-settlement)
   anchors: []
   utility: none
   digest: Equatorial Wigner distance multiplies; nonpositive self-tensors are superadditive. -/
/-
proof_shape: resultEquatorial: content; resultSelfTensor: content
escape_witness: Enumeration.certificate (exhaustive rational dual bound on 60 candidates);
  stabilizer_two_dual_bound (actual subgroup to rational certificate bridge);
  WignerSimplexNearestEdge.nearest_edge_point (explicit convex mixtures);
  spectral_stabilizer, spectral_product_stabilizer (actual local and tensor subgroups);
  tensor_distance_lower (sign-pattern selection and convex weak duality);
  free_one_geometry (subgroup classification and convex positivity);
  free_product_inclusion (two-stage convex tensor closure);
  distance_one_nonpositive (attaining mixture and matching weak duality).
admission_basis: open-problem-resolution (#11541; Proved ×2)
Direct frozen dependencies:
  D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence (owner module; statement id tracked by its canonical pin).
  D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.pauliSet
    statement_id: sha256:856f9c10bdadcb60566b2de31e839e712c75cb4be32af461b413c9fdc95a1014
  D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence (owner module; statement id tracked by its canonical pin).
  D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.pauliMatrix
    statement_id: sha256:7f853eaeda888a9eccbab5fe25474fc62b519a3229013530986887de25cb28d7
  D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.instFintypePauli
    statement_id: sha256:86b778dc124feee0fe09eb37727ded0ed70c523451613e21523f2ee58963ccfd
  D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.instDecidableEqPauli
    statement_id: sha256:33c12f5e37295acca8f6d08be0dd7c7dff2c7a3f0389f74e6c56155c84d61cc8
  D5/S3/Quantum/FiniteDimensional (module statement_id sha256:8448b6959a48d5c232600cbaa512d3eae6aadd57de71f1e30aad67fde1d1b63d).
  D5/S3/Quantum/FiniteDimensional.QubitMatrix
    statement_id: sha256:e376bbe008ddbbc49fcf9763247304ed70ec54ac5cf49af3c6f7fb58fa626f30
  D5/S3/Quantum/FiniteDimensional.bornProbability
    statement_id: sha256:70d0693159ac58607261fa66304a04ba6078de3492431f14485817d5497d9d6d
  D5/S3/Quantum/FiniteDimensional.born_probability_skeleton
    statement_id: sha256:23ce2a1f8e999242868864e28a8bf0653ddac0dbc9455b6bf5795fa62fd1e2cc
  D5/S3/Quantum/FiniteDimensional.qubitX
    statement_id: sha256:cfaddf4a17693b52013e93be8cd6559e7021ed57ca0305492712468b57f882f7
  D5/S3/Quantum/FiniteDimensional.qubitZ
    statement_id: sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c
  D5/S3/QuantumBounds/CHSHWitness (module statement_id sha256:0b256a55db0859d4a6703ba970f7ff6eefd46196b707e4e28e0bdf62e7529e5f).
  D5/S3/QuantumBounds/CHSHWitness.TwoQubitMatrix
    statement_id: sha256:2a939b5c081cb7f5071bf116c5a5967adc0c05361ef9b701465cb9cb84dc1c22
  D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation (module statement_id sha256:53144be34b3e30df21d2cd670b487c2ce7c52c7708571dd55118ea3672fbaa70).
  D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsDensity
    statement_id: sha256:4ba4e6b5fd69f7af3d48c8ecc93d1d3efe0fbd32799aa8b021b502f76ad76988
Information-escape registration is paused under CLAUDE.md §3.9.
-/
import D5.S3.Quantum.Magic.WignerSimplexNearestEdge
import D5.S3.Quantum.Magic.WignerDistanceMinimum
import D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence
import D5.S3.QuantumBounds.CHSHWitness
import D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
noncomputable section
namespace D5.S3.Quantum.Magic.QubitWignerDistanceTensorRules
open Matrix Complex
open D5.S3.Quantum.Magic.WignerSimplexNearestEdge (edgeVertex freeEdges nearest_edge_point)
open D5.S3.QuantumBounds.CHSHWitness (TwoQubitMatrix)
open D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsDensity)
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence (pauliSet plab)
open scoped Kronecker ComplexOrder
open D5.S3.Quantum.Magic.WignerDistanceMinimum
  (PhasePoint phasePoint phasePointTwo Wigner WignerOne WignerTwo pauliTwo Stab Wfree COne CTwo
    spectral eigenVector spectral_stabilizer spectral_product_stabilizer)
def bloch (ρ : QubitMatrix) (p : Pauli) : ℝ := (ρ * pauliMatrix p).trace.re
def claimEquatorial : Prop := ∀ ρ σ : QubitMatrix,
  IsDensity ρ → IsDensity σ → bloch ρ .Z = 0 → bloch σ .Z = 0 →
  CTwo (ρ ⊗ₖ σ) = COne ρ + COne σ + COne ρ * COne σ
def claimSelfTensor : Prop := ∀ ρ : QubitMatrix, IsDensity ρ →
  bloch ρ .X * bloch ρ .Y * bloch ρ .Z ≤ 0 → CTwo (ρ ⊗ₖ ρ) ≥ 2 * COne ρ
/-- The four affine coordinates of the paper's Wootters frame. -/
private def wignerBloch (x y z : ℝ) : Fin 4 → ℝ :=
  ![(1+x+y+z)/4, (1-x-y+z)/4, (1+x-y-z)/4, (1-x+y-z)/4]
namespace Enumeration
abbrev Word := Fin 4 × Fin 4
private def labelProduct (p q : Fin 4) : Fin 4 :=
  (![![0,1,2,3], ![1,0,3,2], ![2,3,0,1], ![3,2,1,0]] : Fin 4 → Fin 4 → Fin 4) p q
private def phaseProduct (p q : Fin 4) : ℕ :=
  (![![0,0,0,0], ![0,0,1,3], ![0,3,0,1], ![0,1,3,0]] : Fin 4 → Fin 4 → ℕ) p q
def commutingIndependent (u v : Word) : Prop :=
  u ≠ (0,0) ∧ v ≠ (0,0) ∧ u ≠ v ∧
    (phaseProduct u.1 v.1 + phaseProduct u.2 v.2) % 2 = 0
private def character (p : Fin 4) (a : PhasePoint) : ℚ :=
  (![1, (-1 : ℚ) ^ (a.2 : ℕ), (-1 : ℚ) ^ ((a.1 : ℕ)+(a.2 : ℕ)),
    (-1 : ℚ) ^ (a.1 : ℕ)] : Fin 4 → ℚ) p
def candidate (u v : Word) (ε δ : Fin 2) (a : PhasePoint × PhasePoint) : ℚ :=
  (1 + (-1 : ℚ) ^ (ε : ℕ) * character u.1 a.1 * character u.2 a.2 +
    (-1 : ℚ) ^ (δ : ℕ) * character v.1 a.1 * character v.2 a.2 +
    (-1 : ℚ) ^ ((ε : ℕ) + (δ : ℕ)) *
      (if (phaseProduct u.1 v.1 + phaseProduct u.2 v.2) % 4 = 0 then 1 else -1) *
      character (labelProduct u.1 v.1) a.1 * character (labelProduct u.2 v.2) a.2) / 16
def candidates : Finset (PhasePoint × PhasePoint → ℚ) :=
  letI (u v : Word) : Decidable (commutingIndependent u v) := inferInstanceAs
    (Decidable (u ≠ (0,0) ∧ v ≠ (0,0) ∧ u ≠ v ∧ (phaseProduct u.1 v.1 + phaseProduct u.2 v.2) % 2 = 0))
  ((Finset.univ : Finset ((Word × Word) × (Fin 2 × Fin 2))).filter
    (fun k => commutingIndependent k.1.1 k.1.2)).image
      (fun k => candidate k.1.1 k.1.2 k.2.1 k.2.2)
private def dualSign (k : Fin 5) (a : PhasePoint) : ℚ :=
  if k.val = 2 * (a.1 : ℕ) + (a.2 : ℕ) then -1 else 1
private def word (u : Word) : TwoQubitMatrix := pauliMatrix (plab u.1) ⊗ₖ pauliMatrix (plab u.2)
def projector (u v : Word) (ε δ : Fin 2) : TwoQubitMatrix :=
  (1/4 : ℂ) • (1 + ((-1 : ℂ) ^ (ε : ℕ)) • word u +
    ((-1 : ℂ) ^ (δ : ℕ)) • word v +
    (((-1 : ℂ) ^ (ε : ℕ)) • word u) * (((-1 : ℂ) ^ (δ : ℕ)) • word v))
private def digit : Pauli → Fin 4 | .I => 0 | .X => 1 | .Y => 2 | .Z => 3
private theorem certificate : candidates.card = 60 ∧ ∀ w ∈ candidates, ∀ f g : Fin 5, (∑ a : PhasePoint × PhasePoint, dualSign f a.1 * dualSign g a.2 * w a) ≤ 1 := by
  decide +kernel
end Enumeration
open Enumeration in
theorem stabilizer_two_generators (ρ : TwoQubitMatrix) (hρ : ρ ∈ Stab pauliTwo) : ∃ (u v : Enumeration.Word) (ε δ : Fin 2), Enumeration.commutingIndependent u v ∧ ρ = Enumeration.projector u v ε δ := by
  have stabilizer_two_shape (ρ : TwoQubitMatrix) (hρ : ρ ∈ Stab pauliTwo) : ∃ P Q : TwoQubitMatrix, P ∈ pauliTwo ∧ Q ∈ pauliTwo ∧ P ≠ 1 ∧ Q ≠ 1 ∧ P ≠ Q ∧ P * Q = Q * P ∧ P*P = 1 ∧ Q*Q = 1 ∧ P*ρ = ρ ∧ Q*ρ = ρ ∧ ρ = (1/4 : ℂ) • (1 + P + Q + P*Q) := by
    have group_average_projector (S : Subgroup (Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ)) [Fintype S] (ψ : (Fin 2 × Fin 2) → ℂ) (hnorm : (∑ i, ‖ψ i‖ ^ 2) = 1) (hunique : ∀ v : (Fin 2 × Fin 2) → ℂ, (∀ g : S, (g.val.val : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) *ᵥ v = v) ↔ ∃ c : ℂ, v = c • ψ) : ((Fintype.card S : ℂ)⁻¹) • (∑ g : S, (g.val.val : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) = Matrix.vecMulVec ψ (star ψ) := by
      classical
      let U (g : S) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := g.val.val; let Q : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := (Fintype.card S : ℂ)⁻¹ • ∑ g : S, U g; have card_ne : (Fintype.card S : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      have hmul (g h : S) : U (g*h) = U g * U h := rfl; have hinv (g : S) : U g⁻¹ = star (U g) := rfl; have hfix (g : S) : U g *ᵥ ψ = ψ := (hunique ψ).mpr ⟨1,by simp⟩ g
      have hleft (g : S) : U g * Q = Q := by
        dsimp [Q]; rw [Matrix.mul_smul, Finset.mul_sum]; simp_rw [← hmul]
        congr 1
        exact Fintype.sum_equiv (Equiv.mulLeft g) (fun h => U (g*h)) U (fun h => rfl)
      have hQfix : Q *ᵥ ψ = ψ := by
        dsimp [Q]; rw [Matrix.smul_mulVec, Matrix.sum_mulVec]; simp_rw [hfix]; ext i; simp [Pi.mul_apply, card_ne]
      have hQstar : star Q = Q := by
        dsimp [Q]; have hscalar : star ((Fintype.card S : ℂ)⁻¹) = (Fintype.card S : ℂ)⁻¹ := by simp
        rw [star_smul, hscalar, star_sum]; simp_rw [← hinv]
        congr 1
        exact Fintype.sum_equiv (Equiv.inv S) (fun g => U g⁻¹) U (fun g => rfl)
      have hcol (j : (Fin 2 × Fin 2)) : ∃ c : ℂ, (fun i => Q i j) = c • ψ := by
        apply (hunique _).mp; intro g; ext i
        exact congrArg (fun M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ => M i j) (hleft g)
      have hinner (j : (Fin 2 × Fin 2)) : (∑ k, star (ψ k) * Q k j) = star (ψ j) := by
        have hj := congrArg (fun v : (Fin 2 × Fin 2) → ℂ => star (v j)) hQfix; simp only [Matrix.mulVec, dotProduct, star_sum, star_mul] at hj; have hentry (k : (Fin 2 × Fin 2)) : star (Q j k) = Q k j :=
          congrArg (fun M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ => M k j) hQstar
        simp_rw [hentry] at hj
        simpa only [mul_comm] using hj
      change Q = _; ext i j; obtain ⟨c,hc⟩ := hcol j; have hjnorm : (∑ k, star (ψ k) * ψ k) = 1 := by
        calc
          (∑ k, star (ψ k) * ψ k) = ∑ k, ((‖ψ k‖ ^ 2 : ℝ) : ℂ) := by
            apply Finset.sum_congr rfl; intro k hk; rw [mul_comm]; simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
          _ = 1 := by exact_mod_cast hnorm
      have hscalar : c = star (ψ j) := by
        have hh := hinner j; simp_rw [congrFun hc, Pi.smul_apply, smul_eq_mul] at hh; simp_rw [← mul_assoc, mul_comm (star (ψ _)) c, mul_assoc] at hh; rw [← Finset.mul_sum, hjnorm, mul_one] at hh
        exact hh
      have hci := congrFun hc i
      simpa [hscalar, Matrix.vecMulVec, mul_comm] using hci
    classical
    rcases hρ with ⟨S,ψ,hP,hcard,hcomm,hnorm,hunique,rfl⟩; have hcard4 : Nat.card S = 4 := by simpa using hcard
    letI : Finite S := Nat.finite_of_card_ne_zero (by omega)
    letI : Fintype S := Fintype.ofFinite S
    have hcardF : Fintype.card S = 4 := by simpa only [Nat.card_eq_fintype_card] using hcard4
    let U (g : S) : TwoQubitMatrix := g.val.val; have hψne : ψ ≠ 0 := by intro hzero; simp [hzero] at hnorm
    have hψfix (g : S) : U g *ᵥ ψ = ψ := (hunique ψ).mpr ⟨1,by simp⟩ g
    have hsingle (p : Pauli) : pauliMatrix p * pauliMatrix p = 1 := by
      cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;>
        norm_num [pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.ofNat_apply, Complex.ext_iff]
    have hsquare (g : S) : g*g = 1 := by
      rcases hP g with ⟨c,hc,p,q,heq⟩; have hpq : (pauliMatrix p ⊗ₖ pauliMatrix q) * (pauliMatrix p ⊗ₖ pauliMatrix q) = 1 := by
        rw [← Matrix.mul_kronecker_mul,hsingle,hsingle,Matrix.one_kronecker_one]
      have hmatrix : U g * U g = (c*c) • (1 : TwoQubitMatrix) := by
        dsimp [U]; rw [heq,Matrix.smul_mul,Matrix.mul_smul,smul_smul,hpq]
      have himpossible (hi : c = Complex.I ∨ c = -Complex.I) : False := by
        have htwice := congrArg (fun v => U g *ᵥ v) (hψfix g); rw [Matrix.mulVec_mulVec,hmatrix,hψfix] at htwice; have hneg : c*c = -1 := by rcases hi with rfl | rfl <;> simp
        rw [hneg,Matrix.smul_mulVec,Matrix.one_mulVec] at htwice; apply hψne; ext i; have hi := congrFun htwice i; simp only [Pi.smul_apply,smul_eq_mul,neg_one_mul,Pi.zero_apply] at hi ⊢
        linear_combination (-1/2 : ℂ) * hi
      apply Subtype.ext; apply Subtype.ext; change U g * U g = 1; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hc; rcases hc with rfl | rfl | hc | hc
      · simpa using hmatrix
      · simpa using hmatrix
      · exact (himpossible (Or.inl hc)).elim
      · exact (himpossible (Or.inr hc)).elim
    letI : Nontrivial S := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨g,hg⟩ := exists_ne (1 : S); obtain ⟨h,hhmem,hhnot⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({1,g} : Finset S)) (t := Finset.univ) (by
        have hsmall : ({1,g} : Finset S).card ≤ 2 := by simp [Ne.symm hg]
        simp only [Finset.card_univ,hcardF]
        omega)
    have hh1 : h ≠ 1 := by intro heq; apply hhnot; simp [heq]
    have hhg : h ≠ g := by intro heq; apply hhnot; simp [heq]
    have hgh1 : g*h ≠ 1 := by
      intro heq; have hhg' : h = g := by
        have heq' := congrArg (fun x : S => g*x) heq
        simpa [← mul_assoc,hsquare] using heq'
      exact hhg hhg'
    have hghg : g*h ≠ g := by
      intro heq; have := mul_left_cancel (show g*h = g*1 by simpa using heq)
      exact hh1 this
    have hghh : g*h ≠ h := by
      intro heq; have := mul_right_cancel (show g*h = 1*h by simpa using heq)
      exact hg this
    have hB : ({1,g,h,g*h} : Finset S) = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _); simp [hcardF,hg,hh1,hhg,hgh1,hghg,hghh,Ne.symm hg,Ne.symm hh1,Ne.symm hhg, Ne.symm hgh1,Ne.symm hghg,Ne.symm hghh]
    have hsum : (∑ k : S, U k) = 1 + U g + U h + U g * U h := by
      rw [← hB]; simp [hg,hh1,hhg,hgh1,hghg,hghh,Ne.symm hg,Ne.symm hh1,Ne.symm hhg, Ne.symm hgh1,Ne.symm hghg,Ne.symm hghh,U]
      abel
    have hprojector := group_average_projector S ψ hnorm hunique; have hne1 (k : S) (hk : k ≠ 1) : U k ≠ 1 := by
      intro heq; apply hk; apply Subtype.ext; apply Subtype.ext; exact heq
    have hdistinct : U g ≠ U h := by
      intro heq; apply hhg; apply Subtype.ext; apply Subtype.ext; exact heq.symm
    refine ⟨U g,U h,hP g,hP h,hne1 g hg,hne1 h hh1,hdistinct,?_,?_,?_,?_,?_,?_⟩
    · exact congrArg (fun k : S => U k) (hcomm g h)
    · exact congrArg (fun k : S => U k) (hsquare g)
    · exact congrArg (fun k : S => U k) (hsquare h)
    · rw [Matrix.mul_vecMulVec,hψfix]
    · rw [Matrix.mul_vecMulVec,hψfix]
    · change _ = (1/4 : ℂ) • _
      have heqAvg : Matrix.vecMulVec ψ (star ψ) = (Fintype.card S : ℂ)⁻¹ • ∑ k : S, U k :=
        hprojector.symm
      rw [hsum,hcardF] at heqAvg
      simpa using heqAvg
  classical
  rcases stabilizer_two_shape ρ hρ with ⟨P,Q,hP,hQ,hPne,hQne,hPQ,hcomm,hP2,hQ2,hPfix,hQfix,hproj⟩; have htrace : ρ.trace = 1 := by
    rcases hρ with ⟨S,ψ,hPauli,hcard,hcomm,hnorm,hunique,rfl⟩
    calc
      (Matrix.vecMulVec ψ (star ψ)).trace = ∑ i, (‖ψ i‖ ^ 2 : ℝ) := by
        simp [Matrix.trace, Matrix.vecMulVec, ← Complex.normSq_eq_norm_sq,Complex.mul_conj]
      _ = 1 := by exact_mod_cast hnorm
  have hsquare (p : Pauli) : pauliMatrix p * pauliMatrix p = 1 := by
    cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [pauliMatrix,qubitX,qubitZ,Matrix.mul_apply,Fin.sum_univ_two, Matrix.ofNat_apply,Complex.ext_iff]
  have hsign (T : TwoQubitMatrix) (hT : T ∈ pauliTwo) (hT2 : T*T = 1) : ∃ (p q : Pauli) (ε : Fin 2), T = ((-1 : ℂ) ^ (ε : ℕ)) • (pauliMatrix p ⊗ₖ pauliMatrix q) := by
    rcases hT with ⟨c,hc,p,q,heq⟩; have hsq : T*T = (c*c) • (1 : TwoQubitMatrix) := by
      rw [heq,Matrix.smul_mul,Matrix.mul_smul,smul_smul,← Matrix.mul_kronecker_mul, hsquare,hsquare,Matrix.one_kronecker_one]
    rw [hT2] at hsq; have hc2 : c*c = 1 := by
      have hd := congrArg (fun M : TwoQubitMatrix => M (0,0) (0,0)) hsq
      simpa using hd.symm
    refine ⟨p,q,?_⟩; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hc; rcases hc with rfl | rfl | rfl | rfl
    · exact ⟨0,by simpa using heq⟩
    · exact ⟨1,by simpa using heq⟩
    · norm_num at hc2
    · norm_num at hc2
  obtain ⟨p,q,ε,heqP⟩ := hsign P hP hP2; obtain ⟨r,s,δ,heqQ⟩ := hsign Q hQ hQ2
  have nonidentity_word (T : TwoQubitMatrix) (hTne : T ≠ 1) (hTfix : T*ρ = ρ) (p q : Pauli) (ε : Fin 2) (heq : T = ((-1 : ℂ) ^ (ε : ℕ)) • (pauliMatrix p ⊗ₖ pauliMatrix q)) : (p,q) ≠ (Pauli.I,Pauli.I) := by
    intro heqword; have hp : p = .I := congrArg Prod.fst heqword; have hq : q = .I := congrArg Prod.snd heqword; subst p; subst q
    fin_cases ε
    · apply hTne; simpa [pauliMatrix] using heq
    · rw [heq] at hTfix
      have ht := congrArg Matrix.trace hTfix; norm_num [pauliMatrix,htrace] at ht
  have hup := nonidentity_word P hPne hPfix p q ε heqP; have hvp := nonidentity_word Q hQne hQfix r s δ heqQ; have hpqrs : (p,q) ≠ (r,s) := by
    intro heqword; have hp : p = r := congrArg Prod.fst heqword; have hq : q = s := congrArg Prod.snd heqword; subst r; subst s
    by_cases hεδ : ε = δ
    · subst δ; apply hPQ; rw [heqP,heqQ]
    · have hn : P = -Q := by
        fin_cases ε <;> fin_cases δ <;> simp_all
      rw [hn,Matrix.neg_mul,hQfix] at hPfix; have ht := congrArg Matrix.trace hPfix; norm_num [htrace] at ht
  have hdigit (p : Pauli) : pauliMatrix (plab (Enumeration.digit p)) = pauliMatrix p := by
    cases p <;> simp [plab,Enumeration.digit,Matrix.cons_val_two, Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  have hdigitinj : Function.Injective Enumeration.digit := by
    intro p q h; cases p <;> cases q <;> simp_all [Enumeration.digit]
  let u : Enumeration.Word := (Enumeration.digit p,Enumeration.digit q); let v : Enumeration.Word := (Enumeration.digit r,Enumeration.digit s); have hu0 : u ≠ (0,0) := by
    intro hh; apply hup
    exact Prod.ext (hdigitinj (congrArg Prod.fst hh)) (hdigitinj (congrArg Prod.snd hh))
  have hv0 : v ≠ (0,0) := by
    intro hh; apply hvp
    exact Prod.ext (hdigitinj (congrArg Prod.fst hh)) (hdigitinj (congrArg Prod.snd hh))
  have huv : u ≠ v := by
    intro hh; apply hpqrs
    exact Prod.ext (hdigitinj (congrArg Prod.fst hh)) (hdigitinj (congrArg Prod.snd hh))
  have hplain : Enumeration.word u * Enumeration.word v = Enumeration.word v * Enumeration.word u := by
    have hc : ((-1 : ℂ) ^ (ε : ℕ)) * ((-1 : ℂ) ^ (δ : ℕ)) ≠ 0 := by positivity
    rw [heqP,heqQ,Matrix.smul_mul,Matrix.mul_smul,smul_smul, Matrix.smul_mul,Matrix.mul_smul,smul_smul, mul_comm ((-1 : ℂ) ^ (δ : ℕ)) ((-1 : ℂ) ^ (ε : ℕ))] at hcomm; have hh := congrArg (fun M : TwoQubitMatrix =>
      (((-1 : ℂ) ^ (ε : ℕ)) * ((-1 : ℂ) ^ (δ : ℕ)))⁻¹ • M) hcomm
    simp only [smul_smul,inv_mul_cancel₀ hc,one_smul] at hh
    simpa [u,v,Enumeration.word,hdigit] using hh
  have hparity : (Enumeration.phaseProduct u.1 v.1 + Enumeration.phaseProduct u.2 v.2) % 2 = 0 := by
    cases p <;> cases q <;> cases r <;> cases s <;>
      norm_num [u,v,Enumeration.digit,Enumeration.phaseProduct,Matrix.cons_val_two, Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
    all_goals
      have hentries : ∀ i j, (Enumeration.word u * Enumeration.word v) i j = (Enumeration.word v * Enumeration.word u) i j :=
        fun i j => congrArg (fun M : TwoQubitMatrix => M i j) hplain
      norm_num [u,v,Enumeration.word,plab,Enumeration.digit, Matrix.ext_iff,Prod.forall,Fin.forall_fin_succ,Matrix.kroneckerMap_apply, pauliMatrix,qubitX,qubitZ,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_two, Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons, Matrix.ofNat_apply,Matrix.one_apply,Complex.ext_iff,Matrix.vecMul,dotProduct] at hentries
  refine ⟨u,v,ε,δ,⟨hu0,hv0,huv,hparity⟩,?_⟩
  simpa only [Enumeration.projector,Enumeration.word,u,v,hdigit,← heqP,← heqQ] using hproj
open Enumeration in
theorem projector_wigner (u v : Enumeration.Word) (ε δ : Fin 2) (h : Enumeration.commutingIndependent u v) : WignerTwo (Enumeration.projector u v ε δ) = fun a => (Enumeration.candidate u v ε δ a : ℝ) := by
  have hchar (i : Fin 4) (a : PhasePoint) : (pauliMatrix (plab i) * phasePoint a).trace = (character i a : ℂ) := by
    rcases a with ⟨q,p⟩
    fin_cases i <;> fin_cases q <;> fin_cases p <;>
      norm_num [plab,character,phasePoint,pauliMatrix,qubitX,qubitZ,Matrix.trace, Matrix.mul_apply,Fin.sum_univ_two,Matrix.ofNat_apply,Complex.ext_iff,Matrix.vecMul,dotProduct, Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  have hprod (i j : Fin 4) : pauliMatrix (plab i) * pauliMatrix (plab j) = Complex.I ^ phaseProduct i j • pauliMatrix (plab (labelProduct i j)) := by
    fin_cases i <;> fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;>
      norm_num [plab,phaseProduct,labelProduct,pauliMatrix,qubitX,qubitZ, Matrix.mul_apply,Fin.sum_univ_two,Matrix.ofNat_apply,Complex.ext_iff,Matrix.vecMul,dotProduct, Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  have hwordprod : word u * word v = Complex.I ^ (phaseProduct u.1 v.1 + phaseProduct u.2 v.2) • word (labelProduct u.1 v.1,labelProduct u.2 v.2) := by
    simp only [word]; rw [← Matrix.mul_kronecker_mul,hprod,hprod,Matrix.smul_kronecker,Matrix.kronecker_smul]; simp only [smul_smul,← pow_add]
  have hphase : Complex.I ^ (phaseProduct u.1 v.1 + phaseProduct u.2 v.2) = (if (phaseProduct u.1 v.1 + phaseProduct u.2 v.2) % 4 = 0 then 1 else -1 : ℂ) := by
    rcases u with ⟨p,q⟩; rcases v with ⟨r,s⟩
    fin_cases p <;> fin_cases q <;> fin_cases r <;> fin_cases s <;>
      norm_num [commutingIndependent,phaseProduct,Matrix.cons_val_two,Matrix.cons_val_three, Matrix.head_cons,Matrix.tail_cons] at h <;>
      norm_num [phaseProduct,Matrix.cons_val_two,Matrix.cons_val_three, Matrix.head_cons,Matrix.tail_cons, pow_succ]
  have hwordtrace (t : Word) (a : PhasePoint × PhasePoint) : (word t * phasePointTwo a).trace = (character t.1 a.1 : ℂ) * (character t.2 a.2 : ℂ) := by
    simp only [word,phasePointTwo]; rw [← Matrix.mul_kronecker_mul,Matrix.trace_kronecker,hchar,hchar]
  have htraceone (a : PhasePoint × PhasePoint) : (phasePointTwo a).trace = 1 := by
    have hx := hwordtrace (0,0) a
    simpa [word,plab,character,pauliMatrix,Matrix.one_kronecker_one] using hx
  ext a; simp only [WignerTwo,Wigner,projector,Matrix.smul_mul,Matrix.mul_smul,smul_smul, Matrix.add_mul,Matrix.one_mul,Matrix.trace_smul,Matrix.trace_add,hwordprod,hphase, hwordtrace,htraceone]
  norm_num [Fintype.card_prod,Fintype.card_fin,smul_eq_mul,candidate]
  split_ifs <;> fin_cases ε <;> fin_cases δ <;>
    norm_num [Complex.mul_re,Complex.mul_im] <;> push_cast <;> ring
open Enumeration in
theorem candidate_mem (u v : Enumeration.Word) (ε δ : Fin 2) (h : Enumeration.commutingIndependent u v) : Enumeration.candidate u v ε δ ∈ Enumeration.candidates := by
  letI (u v : Word) : Decidable (commutingIndependent u v) := inferInstanceAs
    (Decidable (u ≠ (0,0) ∧ v ≠ (0,0) ∧ u ≠ v ∧ (phaseProduct u.1 v.1 + phaseProduct u.2 v.2) % 2 = 0))
  apply Finset.mem_image.mpr
  exact ⟨((u,v),(ε,δ)),Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,rfl⟩
set_option maxHeartbeats 4000000 in
open Enumeration in
private theorem stabilizer_two_dual_bound (ρ : TwoQubitMatrix) (hρ : ρ ∈ Stab pauliTwo) (f g : Fin 5) : (∑ a : PhasePoint × PhasePoint, (Enumeration.dualSign f a.1 : ℝ) * (Enumeration.dualSign g a.2 : ℝ) * WignerTwo ρ a) ≤ 1 := by
  obtain ⟨u,v,ε,δ,h,hρproj⟩ := stabilizer_two_generators ρ hρ; have hpoly := projector_wigner u v ε δ h
  have hmem := candidate_mem u v ε δ h
  have hcert := Enumeration.certificate.2 _ hmem f g; rw [hρproj,hpoly]; change (∑ a, (dualSign f a.1 : ℝ) * (dualSign g a.2 : ℝ) *
    (candidate u v ε δ a : ℝ)) ≤ 1
  exact_mod_cast hcert
lemma distance_dual_lower {α : Type} [Fintype α] (F : Set (α → ℝ)) (hF : F.Nonempty) (w f : α → ℝ) (m : ℝ) (hf : ∀ a, |f a| ≤ 1) (hm : ∀ v ∈ F, ∑ a, f a * v a ≤ m) : (∑ a, f a * w a) - m ≤ Metric.infDist (WithLp.toLp 1 w) (WithLp.toLp 1 '' F) := by
  apply (Metric.le_infDist (hF.image (WithLp.toLp 1))).mpr; rintro _ ⟨v,hv,rfl⟩; rw [PiLp.dist_eq_of_L1]; simp only [PiLp.toLp_apply, Real.dist_eq]; have pointwise (a : α) : f a * (w a-v a) ≤ |w a-v a| := by
    calc
      f a * (w a-v a) ≤ |f a * (w a-v a)| := le_abs_self _
      _ = |f a| * |w a-v a| := abs_mul _ _
      _ ≤ 1 * |w a-v a| := mul_le_mul_of_nonneg_right (hf a) (abs_nonneg _)
      _ = |w a-v a| := one_mul _
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => pointwise a); simp only [mul_sub, Finset.sum_sub_distrib] at hsum; have hvbound := hm v hv; linarith
private theorem tensor_distance_lower (ρ σ : QubitMatrix) (hρ : IsDensity ρ) (hσ : IsDensity σ) (hF : (Wfree phasePointTwo pauliTwo).Nonempty) : ‖WithLp.toLp 1 (WignerOne ρ)‖ * ‖WithLp.toLp 1 (WignerOne σ)‖ - 1 ≤ CTwo (ρ ⊗ₖ σ) := by
  have density_wigner_geometry (ρ : QubitMatrix) (hρ : IsDensity ρ) : (∀ p : Pauli, |bloch ρ p| ≤ 1) ∧ (∀ a : PhasePoint, WignerOne ρ a = wignerBloch (bloch ρ .X) (bloch ρ .Y) (bloch ρ .Z) ⟨2 * (a.1 : ℕ) + (a.2 : ℕ), by omega⟩) ∧ (∀ a b : PhasePoint, WignerOne ρ a < 0 → WignerOne ρ b < 0 → a = b) := by
    have at_most_one_negative (x y z : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hz : |z| ≤ 1) (i j : Fin 4) (hi : wignerBloch x y z i < 0) (hj : wignerBloch x y z j < 0) : i = j := by
      rcases abs_le.mp hx with ⟨hx0, hx1⟩; rcases abs_le.mp hy with ⟨hy0, hy1⟩; rcases abs_le.mp hz with ⟨hz0, hz1⟩
      fin_cases i <;> fin_cases j <;>
        simp [wignerBloch] at hi hj ⊢ <;> linarith
    have projections (p : Pauli) (ε : Fin 2) : let E : QubitMatrix := (1 / 2 : ℂ) • (1 + ((-1 : ℂ) ^ (ε : ℕ)) • pauliMatrix p)
        star E = E ∧ E * E = E := by
      cases p <;> fin_cases ε <;> constructor <;>
        ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose, Matrix.ofNat_apply, Complex.ext_iff]
    have hprob := born_probability_skeleton ρ hρ.1 hρ.2; have bounds (p : Pauli) : |bloch ρ p| ≤ 1 := by
      have hp := hprob.2.2 ((1 / 2 : ℂ) • (1 + pauliMatrix p))
        (by simpa using (projections p 0).1) (by simpa using (projections p 0).2)
      have hm := hprob.2.2 ((1 / 2 : ℂ) • (1 - pauliMatrix p))
        (by simpa only [Fin.val_one, pow_one, neg_smul, one_smul, sub_eq_add_neg] using (projections p 1).1) (by simpa only [Fin.val_one, pow_one, neg_smul, one_smul, sub_eq_add_neg] using (projections p 1).2)
      have hp' := hp.1; have hm' := hm.1
      simp only [bornProbability, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_sub, hρ.2, smul_eq_mul, Complex.mul_re] at hp' hm'; norm_num at hp' hm'; rw [abs_le]
      constructor <;> dsimp [bloch] <;> linarith
    have formula (a : PhasePoint) : WignerOne ρ a = wignerBloch (bloch ρ .X) (bloch ρ .Y) (bloch ρ .Z) ⟨2 * (a.1 : ℕ) + (a.2 : ℕ), by omega⟩ := by
      rcases a with ⟨q,p⟩
      fin_cases q <;> fin_cases p <;>
        simp [WignerOne, Wigner, phasePoint, wignerBloch, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one, Matrix.trace_smul, Matrix.trace_add, hρ.2, bloch, smul_eq_mul, Complex.mul_re] <;> ring
    refine ⟨bounds, formula, ?_⟩; intro a b ha hb; rw [formula] at ha hb; have heq := at_most_one_negative _ _ _ (bounds .X) (bounds .Y) (bounds .Z) _ _ ha hb; have hv := congrArg Fin.val heq
    have hab1 : a.1 = b.1 := by apply Fin.ext; dsimp at hv; omega
    have hab2 : a.2 = b.2 := by apply Fin.ext; dsimp at hv; omega
    exact Prod.ext hab1 hab2
  have tensor_wigner_geometry (ρ σ : QubitMatrix) (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) : WignerTwo (ρ ⊗ₖ σ) = (fun a => WignerOne ρ a.1 * WignerOne σ a.2) := by
    have hA (a : PhasePoint) : (phasePoint a).IsHermitian := by
      rcases a with ⟨q,p⟩; fin_cases q <;> fin_cases p <;>
        ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [Matrix.IsHermitian,phasePoint,pauliMatrix,qubitX,qubitZ, Matrix.conjTranspose_apply,Matrix.ofNat_apply,Complex.ext_iff]
    have him (τ : QubitMatrix) (hτ : τ.IsHermitian) (a : PhasePoint) : (τ * phasePoint a).trace.im = 0 := by
      apply Complex.conj_eq_iff_im.mp; change star ((τ * phasePoint a).trace) = _; rw [← Matrix.trace_conjTranspose,Matrix.conjTranspose_mul,hτ.eq,(hA a).eq, Matrix.trace_mul_comm]
    have ht : WignerTwo (ρ ⊗ₖ σ) = (fun a => WignerOne ρ a.1 * WignerOne σ a.2) := by
      ext a; simp only [WignerTwo,WignerOne,Wigner,phasePointTwo,← Matrix.mul_kronecker_mul, Matrix.trace_kronecker,Complex.mul_re,him ρ hρ,him σ hσ]; norm_num [Fintype.card_prod,Fintype.card_fin]; ring
    exact ht
  classical
  have pattern (τ : QubitMatrix) (hτ : IsDensity τ) : ∃ f : Fin 5, ∀ a, (Enumeration.dualSign f a : ℝ) * WignerOne τ a = |WignerOne τ a| := by
    by_cases hn : ∃ a, WignerOne τ a < 0
    · obtain ⟨a,ha⟩ := hn
      refine ⟨⟨2*(a.1 : ℕ)+(a.2 : ℕ),by omega⟩,?_⟩
      intro b
      by_cases hab : a = b
      · subst b
        simp [Enumeration.dualSign,abs_of_neg ha]
      · have hb : 0 ≤ WignerOne τ b := by
          by_contra! hb
          exact hab ((density_wigner_geometry τ hτ).2.2 a b ha hb)
        have hi : 2*(a.1 : ℕ)+(a.2 : ℕ) ≠ 2*(b.1 : ℕ)+(b.2 : ℕ) := by
          intro hh; apply hab; apply Prod.ext <;> apply Fin.ext <;> omega
        simp [Enumeration.dualSign,hi,abs_of_nonneg hb]
    · push_neg at hn
      refine ⟨4,?_⟩; intro a; have hi : (4 : ℕ) ≠ 2*(a.1 : ℕ)+(a.2 : ℕ) := by omega
      simp [Enumeration.dualSign,hi,abs_of_nonneg (hn a)]
  obtain ⟨f,hf⟩ := pattern ρ hρ; obtain ⟨g,hg⟩ := pattern σ hσ; let F : PhasePoint × PhasePoint → ℝ := fun a =>
    (Enumeration.dualSign f a.1 : ℝ) * (Enumeration.dualSign g a.2 : ℝ)
  have hbound : ∀ v ∈ Wfree phasePointTwo pauliTwo, ∑ a, F a * v a ≤ 1 := by
    apply convexHull_min
    · rintro v ⟨τ,hτ,rfl⟩
      exact stabilizer_two_dual_bound τ hτ f g
    · intro x hx y hy a b ha hb hab
      change (∑ i, F i * (a*x i+b*y i)) ≤ 1; simp only [mul_add,Finset.sum_add_distrib]; have he : (∑ i, F i * (a*x i)) = a*(∑ i,F i*x i) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      have he' : (∑ i, F i * (b*y i)) = b*(∑ i,F i*y i) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      rw [he,he']
      calc
        _ ≤ a*1+b*1 := add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
        _ = 1 := by simpa using hab
  have hnorm (a : PhasePoint × PhasePoint) : |F a| ≤ 1 := by
    dsimp [F,Enumeration.dualSign]
    split_ifs <;> norm_num
  have heval : ∑ a, F a * WignerTwo (ρ ⊗ₖ σ) a = ‖WithLp.toLp 1 (WignerOne ρ)‖ * ‖WithLp.toLp 1 (WignerOne σ)‖ := by
    rw [(tensor_wigner_geometry ρ σ hρ.1.isHermitian hσ.1.isHermitian)]; have he (a : PhasePoint × PhasePoint) : F a * (WignerOne ρ a.1 * WignerOne σ a.2) = |WignerOne ρ a.1| * |WignerOne σ a.2| := by
      dsimp [F]
      calc
        _ = ((Enumeration.dualSign f a.1 : ℝ)*WignerOne ρ a.1) *
          ((Enumeration.dualSign g a.2 : ℝ)*WignerOne σ a.2) := by ring
        _ = _ := by rw [hf,hg]
    simp_rw [he]; simp only [PiLp.norm_eq_of_L1, Real.norm_eq_abs, PiLp.toLp_apply]
    exact (Fintype.sum_prod_type (fun a : PhasePoint × PhasePoint =>
      |WignerOne ρ a.1| * |WignerOne σ a.2|)).trans
        (Fintype.sum_mul_sum (fun a : PhasePoint => |WignerOne ρ a|)
          (fun a : PhasePoint => |WignerOne σ a|)).symm
  have hb := distance_dual_lower (Wfree phasePointTwo pauliTwo) hF (WignerTwo (ρ ⊗ₖ σ)) F 1 hnorm hbound
  simpa only [heval,CTwo] using hb
theorem stabilizer_one_classification (ρ : QubitMatrix) (hρ : ρ ∈ Stab pauliSet) : ∃ (p : Pauli) (ε : Fin 2), p ≠ .I ∧ ρ = (1/2 : ℂ) • (1 + ((-1 : ℂ) ^ (ε : ℕ)) • pauliMatrix p) := by
  have single_stabilized_density (ρ : QubitMatrix) (hρ : IsDensity ρ) (c : ℂ) (hc : c ∈ ({1,-1,Complex.I,-Complex.I} : Set ℂ)) (p : Pauli) (hne : c • pauliMatrix p ≠ 1) (hfix : (c • pauliMatrix p) * ρ = ρ) : ∃ ε : Fin 2, p ≠ .I ∧ ρ = (1/2 : ℂ) • (1 + ((-1 : ℂ) ^ (ε : ℕ)) • pauliMatrix p) := by
    have squares : pauliMatrix p * pauliMatrix p = 1 := by
      cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;>
        norm_num [pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.ofNat_apply, Complex.ext_iff]
    have imaginary_false (hi : c = Complex.I ∨ c = -Complex.I) : False := by
      have hsquare : (c • pauliMatrix p) * (c • pauliMatrix p) = -1 := by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, squares]; rcases hi with rfl | rfl <;> simp
      have htwice := congrArg (fun M : QubitMatrix => (c • pauliMatrix p) * M) hfix; rw [← mul_assoc, hsquare, hfix] at htwice; have ht := congrArg Matrix.trace htwice; norm_num [hρ.2] at ht
    obtain ⟨ε, rfl⟩ : ∃ ε : Fin 2, c = (-1 : ℂ) ^ (ε : ℕ) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc; rcases hc with rfl | rfl | hc | hc
      · exact ⟨0, by norm_num⟩
      · exact ⟨1, by norm_num⟩
      · exact (imaginary_false (Or.inl hc)).elim
      · exact (imaginary_false (Or.inr hc)).elim
    refine ⟨ε, ?_, ?_⟩
    · intro hp; subst p
      fin_cases ε
      · simp [pauliMatrix] at hne
      · have ht := congrArg Matrix.trace hfix; norm_num [pauliMatrix, hρ.2] at ht
    ·
      have hherm := hρ.1.isHermitian.eq; have hr := congrArg Complex.re hρ.2; have hi := congrArg Complex.im hρ.2; have h00 := congrArg (fun M : QubitMatrix => (M 0 0).im) hherm
      have h11 := congrArg (fun M : QubitMatrix => (M 1 1).im) hherm; have h01r := congrArg (fun M : QubitMatrix => (M 0 1).re) hherm; have h01i := congrArg (fun M : QubitMatrix => (M 0 1).im) hherm
      have e00r := congrArg (fun M : QubitMatrix => (M 0 0).re) hfix; have e00i := congrArg (fun M : QubitMatrix => (M 0 0).im) hfix; have e01r := congrArg (fun M : QubitMatrix => (M 0 1).re) hfix
      have e01i := congrArg (fun M : QubitMatrix => (M 0 1).im) hfix; have e10r := congrArg (fun M : QubitMatrix => (M 1 0).re) hfix; have e10i := congrArg (fun M : QubitMatrix => (M 1 0).im) hfix
      have e11r := congrArg (fun M : QubitMatrix => (M 1 1).re) hfix; have e11i := congrArg (fun M : QubitMatrix => (M 1 1).im) hfix
      cases p <;> fin_cases ε <;> try {simp [pauliMatrix] at hne}
      all_goals
        norm_num [pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace, Matrix.IsHermitian, Matrix.conjTranspose_apply] at hr hi h00 h11 h01r h01i e00r e00i e01r e01i e10r e10i e11r e11i
        ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
          norm_num [pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.ofNat_apply] <;> linarith
  classical
  rcases hρ with ⟨S,ψ,hP,hcard,hcomm,hnorm,hunique,rfl⟩; have hcard2 : Nat.card S = 2 := by simpa using hcard
  letI : Finite S := Nat.finite_of_card_ne_zero (by omega)
  letI : Fintype S := Fintype.ofFinite S
  have hcardF : Fintype.card S = 2 := by simpa only [Nat.card_eq_fintype_card] using hcard2
  letI : Nontrivial S := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨g,hg⟩ := exists_ne (1 : S); have hgM : (g.val.val : QubitMatrix) ≠ 1 := by
    intro heq; apply hg; apply Subtype.ext; apply Subtype.ext
    exact heq
  rcases hP g with ⟨c,hc,p,hgp⟩; have hψ : (g.val.val : QubitMatrix) *ᵥ ψ = ψ :=
    (hunique ψ).mpr ⟨1,by simp⟩ g
  have hfix : (c • pauliMatrix p) * Matrix.vecMulVec ψ (star ψ) = Matrix.vecMulVec ψ (star ψ) := by
    rw [← hgp,Matrix.mul_vecMulVec,hψ]
  have hdensity : IsDensity (Matrix.vecMulVec ψ (star ψ)) := by
    refine ⟨Matrix.posSemidef_vecMulVec_self_star ψ, ?_⟩
    calc
      (Matrix.vecMulVec ψ (star ψ)).trace = ∑ i, (‖ψ i‖ ^ 2 : ℝ) := by
        simp [Matrix.trace, Matrix.vecMulVec, ← Complex.normSq_eq_norm_sq, Complex.mul_conj]
      _ = 1 := by exact_mod_cast hnorm
  obtain ⟨ε,hp,heq⟩ := single_stabilized_density _ hdensity c hc p (by simpa [hgp] using hgM) hfix
  exact ⟨p,ε,hp,heq⟩
private theorem free_one_geometry : (Wfree phasePoint pauliSet).Nonempty ∧ ∀ w ∈ Wfree phasePoint pauliSet, (∀ a, 0 ≤ w a) ∧ ∑ a, w a = 1 := by
  have hnon : (Wfree phasePoint pauliSet).Nonempty := by
    refine ⟨WignerOne (spectral .Z 0),?_⟩; apply subset_convexHull ℝ _
    exact ⟨spectral .Z 0,(spectral_stabilizer .Z 0 (by decide)).1,rfl⟩
  refine ⟨hnon,?_⟩; apply convexHull_min
  · rintro w ⟨ρ,hρ,rfl⟩
    obtain ⟨p,ε,hp,hρeq⟩ := stabilizer_one_classification ρ hρ; change (∀ a, 0 ≤ WignerOne ρ a) ∧ ∑ a, WignerOne ρ a = 1; change ρ = spectral p ε at hρeq; rw [hρeq]
    constructor
    · intro a
      rcases a with ⟨q,r⟩
      cases p <;> try contradiction
      all_goals fin_cases ε <;> fin_cases q <;> fin_cases r <;>
        norm_num [WignerOne,Wigner,phasePoint,spectral,pauliMatrix,qubitX,qubitZ, Matrix.trace,Matrix.mul_apply,Fin.sum_univ_two,Matrix.ofNat_apply]
    · cases p <;> try contradiction
      all_goals fin_cases ε <;>
        norm_num [WignerOne,Wigner,phasePoint,spectral,pauliMatrix,qubitX,qubitZ, Matrix.trace,Matrix.mul_apply,Fin.sum_univ_two,Fintype.sum_prod_type,Matrix.ofNat_apply]
  · intro x hx y hy a b ha hb hab
    change (∀ i, 0 ≤ a*x i+b*y i) ∧ (∑ i, (a*x i+b*y i)) = 1; refine ⟨?_,?_⟩
    · intro i
      exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
    · rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,hx.2,hy.2]
      simpa using hab
private theorem free_product_inclusion (a b : PhasePoint → ℝ) (ha : a ∈ Wfree phasePoint pauliSet) (hb : b ∈ Wfree phasePoint pauliSet) : (fun ij : PhasePoint × PhasePoint => a ij.1*b ij.2) ∈ Wfree phasePointTwo pauliTwo := by
  have tensor_wigner_geometry (ρ σ : QubitMatrix) (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) : WignerTwo (ρ ⊗ₖ σ) = (fun a => WignerOne ρ a.1 * WignerOne σ a.2) := by
    have hA (a : PhasePoint) : (phasePoint a).IsHermitian := by
      rcases a with ⟨q,p⟩; fin_cases q <;> fin_cases p <;>
        ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [Matrix.IsHermitian,phasePoint,pauliMatrix,qubitX,qubitZ, Matrix.conjTranspose_apply,Matrix.ofNat_apply,Complex.ext_iff]
    have him (τ : QubitMatrix) (hτ : τ.IsHermitian) (a : PhasePoint) : (τ * phasePoint a).trace.im = 0 := by
      apply Complex.conj_eq_iff_im.mp; change star ((τ * phasePoint a).trace) = _; rw [← Matrix.trace_conjTranspose,Matrix.conjTranspose_mul,hτ.eq,(hA a).eq, Matrix.trace_mul_comm]
    have ht : WignerTwo (ρ ⊗ₖ σ) = (fun a => WignerOne ρ a.1 * WignerOne σ a.2) := by
      ext a; simp only [WignerTwo,WignerOne,Wigner,phasePointTwo,← Matrix.mul_kronecker_mul, Matrix.trace_kronecker,Complex.mul_re,him ρ hρ,him σ hσ]; norm_num [Fintype.card_prod,Fintype.card_fin]; ring
    exact ht
  have hs (p : Pauli) (ε : Fin 2) : (spectral p ε).IsHermitian := by
    cases p <;> fin_cases ε <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.IsHermitian,spectral,pauliMatrix,qubitX,qubitZ, Matrix.conjTranspose_apply,Matrix.ofNat_apply,Complex.ext_iff]
  have base (ρ σ : QubitMatrix) (hρ : ρ ∈ Stab pauliSet) (hσ : σ ∈ Stab pauliSet) : (fun ij : PhasePoint × PhasePoint => WignerOne ρ ij.1 * WignerOne σ ij.2) ∈ Wfree phasePointTwo pauliTwo := by
    obtain ⟨p,ε,hp,hρeq⟩ := stabilizer_one_classification ρ hρ; obtain ⟨q,δ,hq,hσeq⟩ := stabilizer_one_classification σ hσ; change ρ = spectral p ε at hρeq; change σ = spectral q δ at hσeq
    rw [hρeq,hσeq,← (tensor_wigner_geometry (spectral p ε) (spectral q δ) (hs p ε) (hs q δ))]; apply subset_convexHull ℝ _
    exact ⟨_,spectral_product_stabilizer p q ε δ hp hq,rfl⟩
  have for_generator (ρ : QubitMatrix) (hρ : ρ ∈ Stab pauliSet) : ∀ b ∈ Wfree phasePoint pauliSet, (fun ij : PhasePoint × PhasePoint => WignerOne ρ ij.1 * b ij.2) ∈ Wfree phasePointTwo pauliTwo := by
    apply convexHull_min
    · rintro v ⟨σ,hσ,rfl⟩; exact base ρ σ hρ hσ
    · intro x hx y hy r s hr hs hrs
      have hc := (convex_convexHull ℝ (Wigner phasePointTwo '' Stab pauliTwo)) hx hy hr hs hrs
      have heq : (fun ij : PhasePoint × PhasePoint => WignerOne ρ ij.1 * ((r • x+s • y) ij.2)) = (r • (fun ij : PhasePoint × PhasePoint => WignerOne ρ ij.1*x ij.2) + s • (fun ij : PhasePoint × PhasePoint => WignerOne ρ ij.1*y ij.2)) := by
        ext ij; simp only [Pi.smul_apply,Pi.add_apply,smul_eq_mul]; ring
      change (fun ij : PhasePoint × PhasePoint => WignerOne ρ ij.1*((r • x+s • y) ij.2)) ∈ Wfree phasePointTwo pauliTwo; rw [heq]
      exact hc
  have hall : ∀ a ∈ Wfree phasePoint pauliSet, (fun ij : PhasePoint × PhasePoint => a ij.1*b ij.2) ∈ Wfree phasePointTwo pauliTwo := by
    apply convexHull_min
    · rintro v ⟨ρ,hρ,rfl⟩; exact for_generator ρ hρ b hb
    · intro x hx y hy r s hr hs hrs
      have hc := (convex_convexHull ℝ (Wigner phasePointTwo '' Stab pauliTwo)) hx hy hr hs hrs
      have heq : (fun ij : PhasePoint × PhasePoint => ((r • x+s • y) ij.1)*b ij.2) = (r • (fun ij : PhasePoint × PhasePoint => x ij.1*b ij.2) + s • (fun ij : PhasePoint × PhasePoint => y ij.1*b ij.2)) := by
        ext ij; simp only [Pi.smul_apply,Pi.add_apply,smul_eq_mul]; ring
      change (fun ij : PhasePoint × PhasePoint => ((r • x+s • y) ij.1)*b ij.2) ∈ Wfree phasePointTwo pauliTwo; rw [heq]
      exact hc
  exact hall a ha
theorem distance_one_nonpositive (ρ : QubitMatrix) (hρ : IsDensity ρ) (hs : bloch ρ .X * bloch ρ .Y * bloch ρ .Z ≤ 0) : ∃ f ∈ Wfree phasePoint pauliSet, ‖WithLp.toLp 1 f‖ = 1 ∧ ‖WithLp.toLp 1 (WignerOne ρ-f)‖ = ‖WithLp.toLp 1 (WignerOne ρ)‖-1 ∧ COne ρ = ‖WithLp.toLp 1 (WignerOne ρ)‖-1 := by
  have negative_branch_wigner_conditions (x y z : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hz : |z| ≤ 1) (hprod : x*y*z ≤ 0) : (∑ i, wignerBloch x y z i) = 1 ∧ (∀ i l : Fin 4, i ≠ l → 0 ≤ wignerBloch x y z i + wignerBloch x y z l ∧ wignerBloch x y z i + wignerBloch x y z l ≤ 1) ∧ (∀ j : Fin 4, (∀ i, wignerBloch x y z j ≤ wignerBloch x y z i) → ∀ i, wignerBloch x y z i + wignerBloch x y z j ≤ 1/2) := by
    rcases abs_le.mp hx with ⟨hx0,hx1⟩; rcases abs_le.mp hy with ⟨hy0,hy1⟩; rcases abs_le.mp hz with ⟨hz0,hz1⟩; have hsum : (∑ i, wignerBloch x y z i) = 1 := by
      norm_num [wignerBloch,Fin.sum_univ_succ]; ring
    refine ⟨hsum,?_,?_⟩
    · intro i l hne
      fin_cases i <;> fin_cases l <;> norm_num at hne
      all_goals constructor <;> norm_num [wignerBloch,Matrix.cons_val_two,Matrix.cons_val_three, Matrix.head_cons,Matrix.tail_cons] <;> linarith
    · intro j hmin i
      by_cases hij : i = j
      · subst i
        have hs := Finset.sum_le_sum (fun l (_ : l ∈ Finset.univ) => hmin l); simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,hsum] at hs; norm_num at hs; linarith
      by_contra! hi
      have hm0 := hmin 0; have hm1 := hmin 1; have hm2 := hmin 2; have hm3 := hmin 3
      fin_cases j <;> fin_cases i <;> norm_num at hij
      all_goals
        norm_num [wignerBloch,Matrix.cons_val_two,Matrix.cons_val_three, Matrix.head_cons,Matrix.tail_cons] at hm0 hm1 hm2 hm3 hi
        first
        | have hxp : 0 < x := by linarith
          have hyp : 0 < y := by linarith
          have hzp : 0 < z := by linarith
          exact (not_le_of_gt (mul_pos (mul_pos hxp hyp) hzp)) hprod
        | have hxn : x < 0 := by linarith
          have hyn : y < 0 := by linarith
          have hzp : 0 < z := by linarith
          exact (not_le_of_gt (mul_pos (mul_pos_of_neg_of_neg hxn hyn) hzp)) hprod
        | have hxn : x < 0 := by linarith
          have hyp : 0 < y := by linarith
          have hzn : z < 0 := by linarith
          have hxy : x*y < 0 := mul_neg_of_neg_of_pos hxn hyp
          exact (not_le_of_gt (mul_pos_of_neg_of_neg hxy hzn)) hprod
        | have hxp : 0 < x := by linarith
          have hyn : y < 0 := by linarith
          have hzn : z < 0 := by linarith
          have hxy : x*y < 0 := mul_neg_of_pos_of_neg hxp hyn
          exact (not_le_of_gt (mul_pos_of_neg_of_neg hxy hzn)) hprod
  have density_wigner_geometry (ρ : QubitMatrix) (hρ : IsDensity ρ) : (∀ p : Pauli, |bloch ρ p| ≤ 1) ∧ (∀ a : PhasePoint, WignerOne ρ a = wignerBloch (bloch ρ .X) (bloch ρ .Y) (bloch ρ .Z) ⟨2 * (a.1 : ℕ) + (a.2 : ℕ), by omega⟩) ∧ (∀ a b : PhasePoint, WignerOne ρ a < 0 → WignerOne ρ b < 0 → a = b) := by
    have at_most_one_negative (x y z : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hz : |z| ≤ 1) (i j : Fin 4) (hi : wignerBloch x y z i < 0) (hj : wignerBloch x y z j < 0) : i = j := by
      rcases abs_le.mp hx with ⟨hx0, hx1⟩; rcases abs_le.mp hy with ⟨hy0, hy1⟩; rcases abs_le.mp hz with ⟨hz0, hz1⟩
      fin_cases i <;> fin_cases j <;>
        simp [wignerBloch] at hi hj ⊢ <;> linarith
    have projections (p : Pauli) (ε : Fin 2) : let E : QubitMatrix := (1 / 2 : ℂ) • (1 + ((-1 : ℂ) ^ (ε : ℕ)) • pauliMatrix p)
        star E = E ∧ E * E = E := by
      cases p <;> fin_cases ε <;> constructor <;>
        ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose, Matrix.ofNat_apply, Complex.ext_iff]
    have hprob := born_probability_skeleton ρ hρ.1 hρ.2; have bounds (p : Pauli) : |bloch ρ p| ≤ 1 := by
      have hp := hprob.2.2 ((1 / 2 : ℂ) • (1 + pauliMatrix p))
        (by simpa using (projections p 0).1) (by simpa using (projections p 0).2)
      have hm := hprob.2.2 ((1 / 2 : ℂ) • (1 - pauliMatrix p))
        (by simpa only [Fin.val_one, pow_one, neg_smul, one_smul, sub_eq_add_neg] using (projections p 1).1) (by simpa only [Fin.val_one, pow_one, neg_smul, one_smul, sub_eq_add_neg] using (projections p 1).2)
      have hp' := hp.1; have hm' := hm.1
      simp only [bornProbability, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_sub, hρ.2, smul_eq_mul, Complex.mul_re] at hp' hm'; norm_num at hp' hm'; rw [abs_le]
      constructor <;> dsimp [bloch] <;> linarith
    have formula (a : PhasePoint) : WignerOne ρ a = wignerBloch (bloch ρ .X) (bloch ρ .Y) (bloch ρ .Z) ⟨2 * (a.1 : ℕ) + (a.2 : ℕ), by omega⟩ := by
      rcases a with ⟨q,p⟩
      fin_cases q <;> fin_cases p <;>
        simp [WignerOne, Wigner, phasePoint, wignerBloch, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one, Matrix.trace_smul, Matrix.trace_add, hρ.2, bloch, smul_eq_mul, Complex.mul_re] <;> ring
    refine ⟨bounds, formula, ?_⟩; intro a b ha hb; rw [formula] at ha hb; have heq := at_most_one_negative _ _ _ (bounds .X) (bounds .Y) (bounds .Z) _ _ ha hb; have hv := congrArg Fin.val heq
    have hab1 : a.1 = b.1 := by apply Fin.ext; dsimp at hv; omega
    have hab2 : a.2 = b.2 := by apply Fin.ext; dsimp at hv; omega
    exact Prod.ext hab1 hab2
  classical
  let e : PhasePoint ≃ Fin 4 := finProdFinEquiv; let w := wignerBloch (bloch ρ .X) (bloch ρ .Y) (bloch ρ .Z); have he (a : PhasePoint) : WignerOne ρ a = w (e a) := by simpa [e, finProdFinEquiv, Nat.add_comm] using (density_wigner_geometry ρ hρ).2.1 a
  have hg := density_wigner_geometry ρ hρ
  have hc := negative_branch_wigner_conditions (bloch ρ .X) (bloch ρ .Y) (bloch ρ .Z)
    (hg.1 .X) (hg.1 .Y) (hg.1 .Z) hs
  obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin 4)) w Finset.univ_nonempty; obtain ⟨k,hk,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 4)) w Finset.univ_nonempty
  have hn (i j : Fin 4) (hi : w i < 0) (hj : w j < 0) : i = j := by
    have hi' : WignerOne ρ (e.symm i) < 0 := by simpa [he] using hi
    have hj' : WignerOne ρ (e.symm j) < 0 := by simpa [he] using hj
    exact e.symm.injective (hg.2.2 _ _ hi' hj')
  obtain ⟨f,hf,herr⟩ := nearest_edge_point w j k hc.1
    (fun i => hmin i (Finset.mem_univ i)) (fun i => hmax i (Finset.mem_univ i)) hc.2.1 hn
    (hc.2.2 j (fun i => hmin i (Finset.mem_univ i)))
  let L : (Fin 4 → ℝ) →ₗ[ℝ] (PhasePoint → ℝ) :=
    { toFun := fun v a => v (e a),map_add' := fun _ _ => rfl,map_smul' := fun _ _ => rfl }
  have hedge : ∀ v ∈ freeEdges, L v ∈ Wfree phasePoint pauliSet := by
    rintro v ⟨i,j,hij,rfl⟩; have hex : ∃ (p : Pauli) (ε : Fin 2), p ≠ .I ∧ L (edgeVertex i j) = WignerOne (spectral p ε) := by
      fin_cases i <;> fin_cases j <;> norm_num at hij
      all_goals solve
      | refine ⟨.X,0,by decide,?_⟩; ext a; rcases a with ⟨q,r⟩; fin_cases q <;> fin_cases r <;>
          norm_num [L,e,finProdFinEquiv,edgeVertex,WignerOne,Wigner,phasePoint,spectral,pauliMatrix,qubitX,qubitZ,Matrix.trace,Matrix.mul_apply,Fin.sum_univ_two,Matrix.ofNat_apply,Fin.mk_eq_mk]
      | refine ⟨.X,1,by decide,?_⟩; ext a; rcases a with ⟨q,r⟩; fin_cases q <;> fin_cases r <;>
          norm_num [L,e,finProdFinEquiv,edgeVertex,WignerOne,Wigner,phasePoint,spectral,pauliMatrix,qubitX,qubitZ,Matrix.trace,Matrix.mul_apply,Fin.sum_univ_two,Matrix.ofNat_apply,Fin.mk_eq_mk]
      | refine ⟨.Y,0,by decide,?_⟩; ext a; rcases a with ⟨q,r⟩; fin_cases q <;> fin_cases r <;>
          norm_num [L,e,finProdFinEquiv,edgeVertex,WignerOne,Wigner,phasePoint,spectral,pauliMatrix,qubitX,qubitZ,Matrix.trace,Matrix.mul_apply,Fin.sum_univ_two,Matrix.ofNat_apply,Fin.mk_eq_mk]
      | refine ⟨.Y,1,by decide,?_⟩; ext a; rcases a with ⟨q,r⟩; fin_cases q <;> fin_cases r <;>
          norm_num [L,e,finProdFinEquiv,edgeVertex,WignerOne,Wigner,phasePoint,spectral,pauliMatrix,qubitX,qubitZ,Matrix.trace,Matrix.mul_apply,Fin.sum_univ_two,Matrix.ofNat_apply,Fin.mk_eq_mk]
      | refine ⟨.Z,0,by decide,?_⟩; ext a; rcases a with ⟨q,r⟩; fin_cases q <;> fin_cases r <;>
          norm_num [L,e,finProdFinEquiv,edgeVertex,WignerOne,Wigner,phasePoint,spectral,pauliMatrix,qubitX,qubitZ,Matrix.trace,Matrix.mul_apply,Fin.sum_univ_two,Matrix.ofNat_apply,Fin.mk_eq_mk]
      | refine ⟨.Z,1,by decide,?_⟩; ext a; rcases a with ⟨q,r⟩; fin_cases q <;> fin_cases r <;>
          norm_num [L,e,finProdFinEquiv,edgeVertex,WignerOne,Wigner,phasePoint,spectral,pauliMatrix,qubitX,qubitZ,Matrix.trace,Matrix.mul_apply,Fin.sum_univ_two,Matrix.ofNat_apply,Fin.mk_eq_mk]
    obtain ⟨p,ε,hp,heq⟩ := hex; rw [heq]
    exact subset_convexHull ℝ _ ⟨spectral p ε,(spectral_stabilizer p ε hp).1,rfl⟩
  have hfree : L f ∈ Wfree phasePoint pauliSet := by
    have hmap : L f ∈ L '' convexHull ℝ freeEdges := ⟨f,hf,rfl⟩; rw [L.image_convexHull] at hmap
    exact convexHull_min (by rintro _ ⟨v,hv,rfl⟩; exact hedge v hv)
      (convex_convexHull ℝ _) hmap
  have hnorm := (free_one_geometry.2 _ hfree); have hl1 : ‖WithLp.toLp 1 (L f)‖ = 1 := by
    simpa only [PiLp.norm_eq_of_L1, Real.norm_eq_abs, PiLp.toLp_apply,abs_of_nonneg (hnorm.1 _)] using hnorm.2
  have hsum (v : Fin 4 → ℝ) : ‖WithLp.toLp 1 (fun a => v (e a))‖ = ‖WithLp.toLp 1 v‖ := by
    simpa only [PiLp.norm_eq_of_L1, Real.norm_eq_abs, PiLp.toLp_apply] using Fintype.sum_equiv e (fun a => |v (e a)|) (fun i => |v i|) (fun _ => rfl)
  have herror : ‖WithLp.toLp 1 (WignerOne ρ-L f)‖ = ‖WithLp.toLp 1 (WignerOne ρ)‖-1 := by
    have hρw : WignerOne ρ = fun a => w (e a) := funext he; rw [hρw]; change ‖WithLp.toLp 1 (fun a => (w-f) (e a))‖ = ‖WithLp.toLp 1 (fun a => w (e a))‖-1; rw [hsum,hsum,herr]
  refine ⟨L f,hfree,hl1,herror,?_⟩; have hup : COne ρ ≤ ‖WithLp.toLp 1 (WignerOne ρ)‖-1 := by
    rw [← herror]; exact (Metric.infDist_le_dist_of_mem (show WithLp.toLp 1 (L f) ∈ WithLp.toLp 1 '' Wfree phasePoint pauliSet from ⟨L f,hfree,rfl⟩)).trans_eq (by simp [PiLp.dist_eq_of_L1, Real.dist_eq, PiLp.norm_eq_of_L1])
  have hlo : ‖WithLp.toLp 1 (WignerOne ρ)‖-1 ≤ COne ρ := by
    let F : PhasePoint → ℝ := fun a => if WignerOne ρ a < 0 then -1 else 1; have hb : ∀ a, |F a| ≤ 1 := by intro a; dsimp [F]; split_ifs <;> norm_num
    have hfval : (∑ a,F a*WignerOne ρ a) = ‖WithLp.toLp 1 (WignerOne ρ)‖ := by
      simp only [PiLp.norm_eq_of_L1, Real.norm_eq_abs, PiLp.toLp_apply]
      apply Finset.sum_congr rfl; intro a _; dsimp [F]; split_ifs with h
      · simp [abs_of_neg h]
      · simp [abs_of_nonneg (le_of_not_gt h)]
    have hfreebound : ∀ v ∈ Wfree phasePoint pauliSet, ∑ a,F a*v a ≤ 1 := by
      intro v hv; have hg := free_one_geometry.2 v hv; rw [← hg.2]; apply Finset.sum_le_sum; intro a _; dsimp [F]; split_ifs <;> nlinarith [hg.1 a]
    have h := distance_dual_lower _ free_one_geometry.1 (WignerOne ρ) F 1 hb hfreebound
    simpa only [hfval,COne] using h
  exact le_antisymm hup hlo
/-- Exact settlement of the equatorial multiplicativity claim using matching primal and dual witnesses. -/
theorem resultEquatorial : claimEquatorial := by
  have tensor_wigner_geometry (ρ σ : QubitMatrix) (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) : WignerTwo (ρ ⊗ₖ σ) = (fun a => WignerOne ρ a.1 * WignerOne σ a.2) := by
    have hA (a : PhasePoint) : (phasePoint a).IsHermitian := by
      rcases a with ⟨q,p⟩; fin_cases q <;> fin_cases p <;>
        ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [Matrix.IsHermitian,phasePoint,pauliMatrix,qubitX,qubitZ, Matrix.conjTranspose_apply,Matrix.ofNat_apply,Complex.ext_iff]
    have him (τ : QubitMatrix) (hτ : τ.IsHermitian) (a : PhasePoint) : (τ * phasePoint a).trace.im = 0 := by
      apply Complex.conj_eq_iff_im.mp; change star ((τ * phasePoint a).trace) = _; rw [← Matrix.trace_conjTranspose,Matrix.conjTranspose_mul,hτ.eq,(hA a).eq, Matrix.trace_mul_comm]
    have ht : WignerTwo (ρ ⊗ₖ σ) = (fun a => WignerOne ρ a.1 * WignerOne σ a.2) := by
      ext a; simp only [WignerTwo,WignerOne,Wigner,phasePointTwo,← Matrix.mul_kronecker_mul, Matrix.trace_kronecker,Complex.mul_re,him ρ hρ,him σ hσ]; norm_num [Fintype.card_prod,Fintype.card_fin]; ring
    exact ht
  have tensor_primal_bound {α β : Type} [Fintype α] [Fintype β] (w a : α → ℝ) (v b : β → ℝ) (ha : ‖WithLp.toLp 1 a‖ = 1) (hb : ‖WithLp.toLp 1 b‖ = 1) : ‖WithLp.toLp 1 (fun ij : α × β => w ij.1 * v ij.2 - a ij.1 * b ij.2)‖ ≤ ‖WithLp.toLp 1 (w-a)‖ + ‖WithLp.toLp 1 (v-b)‖ + ‖WithLp.toLp 1 (w-a)‖ * ‖WithLp.toLp 1 (v-b)‖ := by
    have prod_norm (u : α → ℝ) (t : β → ℝ) : (∑ ij : α × β, |u ij.1 * t ij.2|) = ‖WithLp.toLp 1 u‖ * ‖WithLp.toLp 1 t‖ := by
      simp only [abs_mul, Fintype.sum_prod_type, PiLp.norm_eq_of_L1, Real.norm_eq_abs, PiLp.toLp_apply]
      exact (Fintype.sum_mul_sum _ _).symm
    have hpoint (ij : α × β) : |w ij.1 * v ij.2 - a ij.1 * b ij.2| ≤ |(w ij.1-a ij.1) * b ij.2| + |a ij.1 * (v ij.2-b ij.2)| + |(w ij.1-a ij.1) * (v ij.2-b ij.2)| := by
      have hexp : w ij.1 * v ij.2 - a ij.1 * b ij.2 = (w ij.1-a ij.1) * b ij.2 + a ij.1 * (v ij.2-b ij.2) + (w ij.1-a ij.1) * (v ij.2-b ij.2) := by ring
      rw [hexp]
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
    have hsum := Finset.sum_le_sum (fun ij (_ : ij ∈ Finset.univ) => hpoint ij); simp only [Finset.sum_add_distrib] at hsum
    rw [prod_norm (fun x => w x-a x) b, prod_norm a (fun y => v y-b y), prod_norm (fun x => w x-a x) (fun y => v y-b y), ha,hb] at hsum
    simpa only [PiLp.norm_eq_of_L1, Real.norm_eq_abs, PiLp.toLp_apply, mul_one, one_mul, Pi.sub_def] using hsum
  intro ρ σ hρ hσ hzρ hzσ; have hsρ : bloch ρ .X * bloch ρ .Y * bloch ρ .Z ≤ 0 := by rw [hzρ]; simp
  have hsσ : bloch σ .X * bloch σ .Y * bloch σ .Z ≤ 0 := by rw [hzσ]; simp
  obtain ⟨a,ha,hanorm,herrρ,hCρ⟩ := distance_one_nonpositive ρ hρ hsρ; obtain ⟨b,hb,hbnorm,herrσ,hCσ⟩ := distance_one_nonpositive σ hσ hsσ; have hfree := free_product_inclusion a b ha hb
  have hnon : (Wfree phasePointTwo pauliTwo).Nonempty := ⟨_,hfree⟩; have hlo := tensor_distance_lower ρ σ hρ hσ hnon; have hup : CTwo (ρ ⊗ₖ σ) ≤ COne ρ + COne σ + COne ρ*COne σ := by
    have hdist : CTwo (ρ ⊗ₖ σ) ≤ ‖WithLp.toLp 1 (WignerTwo (ρ ⊗ₖ σ)-(fun ij : PhasePoint × PhasePoint => a ij.1*b ij.2))‖ := by
      exact (Metric.infDist_le_dist_of_mem (show WithLp.toLp 1 (fun ij : PhasePoint × PhasePoint => a ij.1*b ij.2) ∈ WithLp.toLp 1 '' Wfree phasePointTwo pauliTwo from ⟨_,hfree,rfl⟩)).trans_eq (by simp [PiLp.dist_eq_of_L1, Real.dist_eq, PiLp.norm_eq_of_L1])
    rw [(tensor_wigner_geometry ρ σ hρ.1.isHermitian hσ.1.isHermitian)] at hdist; have hp := tensor_primal_bound (WignerOne ρ) a (WignerOne σ) b hanorm hbnorm; have hh := hdist.trans hp
    simpa only [herrρ,herrσ,← hCρ,← hCσ] using hh
  apply le_antisymm hup; rw [hCρ,hCσ]; nlinarith
/-- Exact settlement of the nonpositive-sign self-tensor claim. -/
theorem resultSelfTensor : claimSelfTensor := by
  intro ρ hρ hsρ; obtain ⟨a,ha,hanorm,herrρ,hCρ⟩ := distance_one_nonpositive ρ hρ hsρ; have hfree := free_product_inclusion a a ha ha; have hlo := tensor_distance_lower ρ ρ hρ hρ ⟨_,hfree⟩; rw [hCρ]
  nlinarith [sq_nonneg (‖WithLp.toLp 1 (WignerOne ρ)‖-1)]
#print axioms resultEquatorial
#print axioms resultSelfTensor
end D5.S3.Quantum.Magic.QubitWignerDistanceTensorRules
