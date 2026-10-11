/- GID: D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.claim; result=D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.result; claim=D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation.claim
   digest: A three-qubit ancilla gives stabilizer POVM span dimensions 32 > 31 (2510.00157). -/
/-
proof_shape: result: content
escape_witness: maximal_entangled_support_bound and explicit_lower_bound;
  Pauli expansion, maximality, ancilla-word injectivity and dimension counting.
admission_basis: open-problem-resolution (#11467; Refuted)
Direct frozen dependencies:
  D5/S3/Quantum/FiniteDimensional (module sha256:8448b6959a48d5c232600cbaa512d3eae6aadd57de71f1e30aad67fde1d1b63d)
    qubitX: sha256:cfaddf4a17693b52013e93be8cd6559e7021ed57ca0305492712468b57f882f7
    qubitZ: sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c
  D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence
    pauliMatrix: sha256:7f853eaeda888a9eccbab5fe25474fc62b519a3229013530986887de25cb28d7
    Pauli: sha256:3758fca32bf974298628515ed91492adafcdff8dc216bac5d000b130b08b04fc
    wordOp: sha256:716021b4dbe91f63db8a8ce009e9f85de30e6cc741033f164343fc5ce30653ed
    tensorOp: sha256:0da7fdcc843e3d6cb83079e32e80fde7787e167c84a8fb99695fdb5e9ba7ba8e
    anticomm: sha256:8a615ce73fb1d46bf2c890a9073983597d5f5bbbe2cacb10ef5e37c455cdb3ff
    sgn: sha256:55aa94f381d8c5e38ef1ffe61039768913545c7071f00b0431a45dd922adebe5
    instFintypePauli: sha256:86b778dc124feee0fe09eb37727ded0ed70c523451613e21523f2ee58963ccfd
    phaseZ: sha256:5a97e509499fbf9b6bc0ac954375e0debcae52dafdf220195c9b910028b796ee
  D5/S3/Quantum/Information/SignedPauliSumNormRefutation
    pauliZ: sha256:61ea0b0971de26d2479eb5faaefb162074ffdfe2562ca9621d05f53503521f36
    wordZ: sha256:cd251e1dd9167687215f57ec2224363bba8a2d0ae15466e1fdbc41636a09a3b9
    pauliDigit: sha256:640ce24e5c16f702d406f79e308ba17aa6db2d8f71ac28c1efd18aafa4af0052
  D5/S3/Quantum/PureState/PureStateHandshake
    rankOneDensity: sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3
  D5/S3/Quantum/Reduction/IsometricCompression
    compress: sha256:ece129ea3121d41eb72b96831bf50f675e9fccf3bae2b5d39dc556c28adb9beb
proof_shape: word_expansion: content; span induction constructs the full Pauli expansion of an arbitrary matrix.
proof_shape: maximal_word: content; constructs and verifies an enlarged subgroup, then applies maximality.
proof_shape: projector_in_group_span: content; zero versus nonzero trace branches use the commutant and maximality.
proof_shape: ancilla_injective: content; constructs a data-supported product and uses trivial support to recover equality.
proof_shape: maximal_entangled_support_bound: content; span induction plus an injection yields the cardinality/dimension bound.
proof_shape: standard_maximal: content; constructs the Z word from commuting letters and excludes all other phases.
proof_shape: thirtytwo_in_span: content; chooses distinct surviving ancilla words in the I and Z branches.
proof_shape: explicit_lower_bound: content; constructs 32 independent operators inside the effective span and counts them.
Information-escape registration is paused under CLAUDE.md §3.9.
-/
import D5.S3.Quantum.Information.SignedPauliSumNormRefutation
import D5.S3.Quantum.PureState.PureStateHandshake
import D5.S3.Quantum.Reduction.IsometricCompression
import Mathlib.LinearAlgebra.Matrix.Bilinear
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.style.haveILetI false
namespace D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
open scoped BigOperators
open D5.S3.Quantum.Reduction
open D5.S3.Quantum.Information
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.PureState.PureStateHandshake
open D5.S3.Quantum.Information.SignedPauliSumNormRefutation
abbrev State (n : ℕ) := (Fin n → Fin 2) → ℂ
abbrev Operator (n : ℕ) := Matrix ((Fin n → Fin 2)) ((Fin n → Fin 2)) ℂ
def Phase (c : ℂ) : Prop := c = 1 ∨ c = -1 ∨ c = Complex.I ∨ c = -Complex.I
private def letterProduct : Pauli → Pauli → Pauli | .I, q => q | p, .I => p | .X, .X => .I | .Y, .Y => .I | .Z, .Z => .I | .X, .Y => .Z | .Y, .X => .Z | .X, .Z => .Y | .Z, .X => .Y | .Y, .Z => .X | .Z, .Y => .X
private def letterPhase : Pauli → Pauli → ℂ | .X, .Y => Complex.I | .Y, .Z => Complex.I | .Z, .X => Complex.I | .Y, .X => -Complex.I | .Z, .Y => -Complex.I | .X, .Z => -Complex.I | _, _ => 1
lemma tensor_one {n : ℕ} : tensorOp (fun _ : Fin n => (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by classical
  ext x y; simp only [tensorOp, Matrix.of_apply, Matrix.one_apply, Fintype.prod_boole, ← funext_iff]
def wordUnit {n : ℕ} (w : (Fin n → Pauli)) : (Operator n)ˣ := by
  have tensor_mul {n : ℕ} (M N : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : tensorOp M * tensorOp N = tensorOp fun i => M i * N i := (by classical
    ext x z; simp only [tensorOp, Matrix.mul_apply, Matrix.of_apply]; simp_rw [← Finset.prod_mul_distrib]; rw [Finset.prod_univ_sum, Fintype.piFinset_univ])
  have pauli_sq (p : Pauli) : pauliMatrix p * pauliMatrix p = 1 := (by cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two])
  have word_sq {n : ℕ} (w : (Fin n → Pauli)) : wordOp w * wordOp w = 1 := (by unfold wordOp; rw [tensor_mul]; simp_rw [pauli_sq]; exact tensor_one)
  exact ⟨wordOp w, wordOp w, word_sq w, word_sq w⟩
lemma word_one {n : ℕ} : wordOp (fun _ : Fin n => Pauli.I) = 1 := tensor_one
def pauliGroup (n : ℕ) : Subgroup (Operator n)ˣ := by
  have tensor_one {n : ℕ} : tensorOp (fun _ : Fin n => (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by classical
    ext x y; simp only [tensorOp, Matrix.of_apply, Matrix.one_apply, Fintype.prod_boole, ← funext_iff]
  have phase_ne_zero {c : ℂ} (h : Phase c) : c ≠ 0 := (by rcases h with rfl | rfl | rfl | rfl <;> simp)
  have phase_mul {c d : ℂ} (hc : Phase c) (hd : Phase d) : Phase (c*d) := (by rcases hc with rfl | rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl | rfl <;> simp [Phase, Complex.I_mul_I])
  have phase_inv {c : ℂ} (h : Phase c) : Phase c⁻¹ := (by rcases h with rfl | rfl | rfl | rfl <;> simp [Phase, Complex.inv_I])
  have phase_prod {n : ℕ} (c : Fin n → ℂ) (h : ∀ i, Phase (c i)) : Phase (∏ i, c i) := (by exact Finset.prod_induction _ _ (fun _ _ => phase_mul) (by simp [Phase]) (fun i _ => h i))
  have tensor_mul {n : ℕ} (M N : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : tensorOp M * tensorOp N = tensorOp fun i => M i * N i := (by classical
    ext x z; simp only [tensorOp, Matrix.mul_apply, Matrix.of_apply]; simp_rw [← Finset.prod_mul_distrib]; rw [Finset.prod_univ_sum, Fintype.piFinset_univ])
  have tensor_smul {n : ℕ} (c : Fin n → ℂ) (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : tensorOp (fun i => c i • M i) = (∏ i, c i) • tensorOp M := (by ext x y; simp [tensorOp, Finset.prod_mul_distrib])
  have letter_phase (p q : Pauli) : Phase (letterPhase p q) := (by cases p <;> cases q <;> simp [letterPhase, Phase])
  have letter_mul (p q : Pauli) : pauliMatrix p * pauliMatrix q = letterPhase p q • pauliMatrix (letterProduct p q) := (by cases p <;> cases q <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [letterPhase, letterProduct, pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two])
  have word_mul {n : ℕ} (v w : (Fin n → Pauli)) : wordOp v * wordOp w = (∏ i, letterPhase (v i) (w i)) • wordOp (fun i => letterProduct (v i) (w i)) := (by unfold wordOp; rw [tensor_mul]; simp_rw [letter_mul]; exact tensor_smul _ _)
  exact {
    carrier := {u | ∃ c : ℂ, Phase c ∧ ∃ w : (Fin n → Pauli), (u : Operator n) = c • wordOp w}
    one_mem' := ⟨1, Or.inl rfl, fun _ => Pauli.I, by simp [word_one]⟩
    mul_mem' := by
      rintro u v ⟨c, hc, w, hw⟩ ⟨d, hd, z, hz⟩; refine ⟨c*d*(∏ i, letterPhase (w i) (z i)),
        phase_mul (phase_mul hc hd) (phase_prod _ (fun i => letter_phase _ _)),
        (fun i => letterProduct (w i) (z i)), ?_⟩
      simp only [Units.val_mul, hw, hz, smul_mul_smul, word_mul, smul_smul]
    inv_mem' := by rintro u ⟨c, hc, w, hw⟩; refine ⟨c⁻¹, phase_inv hc, w, ?_⟩; have hu : u = Units.map (algebraMap ℂ (Operator n)).toMonoidHom (Units.mk0 c (phase_ne_zero hc)) * wordUnit w := (by apply Units.ext; simp [Algebra.algebraMap_eq_smul_one, wordUnit, hw]); rw [hu, mul_inv_rev]; simp [wordUnit, Algebra.algebraMap_eq_smul_one, Units.val_mul, smul_mul_smul, mul_smul]
  }
structure StabilizerGroup (n : ℕ) where
  subgroup : Subgroup (Operator n)ˣ
  pauli : subgroup ≤ pauliGroup n
  abelian : ∀ u ∈ subgroup, ∀ v ∈ subgroup, u*v = v*u
  excludes_neg_identity : (-1 : (Operator n)ˣ) ∉ subgroup
  maximal : ∀ T : Subgroup (Operator n)ˣ, T ≤ pauliGroup n →
    (∀ u ∈ T, ∀ v ∈ T, u*v = v*u) → (-1 : (Operator n)ˣ) ∉ T → subgroup ≤ T → T = subgroup
lemma tensor_trace {n : ℕ} (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : Matrix.trace (tensorOp M) = ∏ i, Matrix.trace (M i) := (by classical
  simp only [Matrix.trace, Matrix.diag, tensorOp, Matrix.of_apply]; rw [Finset.prod_univ_sum, Fintype.piFinset_univ])
lemma pauli_trace_pair (p q : Pauli) : Matrix.trace (pauliMatrix p * pauliMatrix q) = if p = q then 2 else 0 := (by cases p <;> cases q <;> simp [pauliMatrix, qubitX, qubitZ, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num)
lemma word_expansion {n : ℕ} (A : Operator n) : A = ∑ w : (Fin n → Pauli), (((2 : ℂ)^n)⁻¹ * Matrix.trace (wordOp w * A)) • wordOp w := by
  have word_trace_pair {n : ℕ} (v w : (Fin n → Pauli)) : Matrix.trace (wordOp v * wordOp w) = if v = w then (2 : ℂ)^n else 0 := by
    have tensor_mul {n : ℕ} (M N : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : tensorOp M * tensorOp N = tensorOp fun i => M i * N i := (by classical
      ext x z; simp only [tensorOp, Matrix.mul_apply, Matrix.of_apply]; simp_rw [← Finset.prod_mul_distrib]; rw [Finset.prod_univ_sum, Fintype.piFinset_univ])
    classical
    unfold wordOp; rw [tensor_mul, tensor_trace]; simp_rw [pauli_trace_pair]
    simp only [Fintype.prod_ite_zero, ← funext_iff, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have word_linearIndependent (n : ℕ) : LinearIndependent ℂ (@wordOp n) := by classical
    apply linearIndependent_iff'.2; intro s c h v hv; have ht := congrArg (fun A : Operator n => Matrix.trace (wordOp v * A)) h; simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, word_trace_pair, mul_ite, mul_zero, Matrix.mul_zero, Matrix.trace_zero] at ht; rw [Finset.sum_ite_eq s v] at ht; simp only [hv, if_true] at ht; exact (mul_eq_zero.mp ht).resolve_right (pow_ne_zero _ (by norm_num))
  have word_span_top (n : ℕ) : Submodule.span ℂ (Set.range (@wordOp n)) = ⊤ := (by apply (word_linearIndependent n).span_eq_top_of_card_eq_finrank'; simp only [Module.finrank_matrix, Module.finrank_self, Fintype.card_fun, Fintype.card_fin, mul_one]; have hp : Fintype.card Pauli = 4 := (by decide); rw [hp, ← mul_pow]; norm_num)
  classical
  have hA : A ∈ Submodule.span ℂ (Set.range (@wordOp n)) := (by rw [word_span_top]; trivial)
  induction hA using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨w, rfl⟩ := hB
    simp only [word_trace_pair, mul_ite, mul_zero, ite_smul, zero_smul]; rw [Finset.sum_ite_eq' Finset.univ w]; simp [pow_ne_zero n (show (2 : ℂ) ≠ 0 by norm_num)]
  | zero => simp
  | add B C _ _ hB hC =>
    simp only [Matrix.mul_add, Matrix.trace_add, mul_add, add_smul, Finset.sum_add_distrib]; rw [← hB, ← hC]
  | smul c B _ hB =>
    simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    nth_rw 1 [hB]
    rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro w _; rw [smul_smul]; congr 1; ring
private lemma maximal_word {n : ℕ} (S : StabilizerGroup n) (w : (Fin n → Pauli)) (hc : ∀ u ∈ S.subgroup, wordUnit w * u = u * wordUnit w) : wordUnit w ∈ S.subgroup ∨ (-1 : (Operator n)ˣ) * wordUnit w ∈ S.subgroup := by
  have tensor_one {n : ℕ} : tensorOp (fun _ : Fin n => (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by classical
    ext x y; simp only [tensorOp, Matrix.of_apply, Matrix.one_apply, Fintype.prod_boole, ← funext_iff]
  have tensor_mul {n : ℕ} (M N : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : tensorOp M * tensorOp N = tensorOp fun i => M i * N i := (by classical
    ext x z; simp only [tensorOp, Matrix.mul_apply, Matrix.of_apply]; simp_rw [← Finset.prod_mul_distrib]; rw [Finset.prod_univ_sum, Fintype.piFinset_univ])
  have pauli_sq (p : Pauli) : pauliMatrix p * pauliMatrix p = 1 := (by cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two])
  have word_sq {n : ℕ} (w : (Fin n → Pauli)) : wordOp w * wordOp w = 1 := (by unfold wordOp; rw [tensor_mul]; simp_rw [pauli_sq]; exact tensor_one)
  have neg_identity_comm {n : ℕ} (u : (Operator n)ˣ) : (-1 : (Operator n)ˣ) * u = u * (-1 : (Operator n)ˣ) := (by apply Units.ext; simp [ Algebra.algebraMap_eq_smul_one])
  classical
  by_contra h
  have hn := not_or.mp h
  let t := wordUnit w
  have ht : t*t = 1 := Units.ext (word_sq w)
  let T := Subgroup.closure ((S.subgroup : Set _) ∪ {t})
  let K : Subgroup (Operator n)ˣ := {
    carrier := {u | u ∈ S.subgroup ∨ ∃ s ∈ S.subgroup, u = t*s}
    one_mem' := Or.inl S.subgroup.one_mem
    mul_mem' := by
      rintro u v (hu | ⟨s, hs, rfl⟩) (hv | ⟨r, hr, rfl⟩)
      · exact Or.inl (S.subgroup.mul_mem hu hv)
      · exact Or.inr ⟨u*r, S.subgroup.mul_mem hu hr, by rw [← mul_assoc, ← hc u hu, mul_assoc]⟩
      · exact Or.inr ⟨s*v, S.subgroup.mul_mem hs hv, mul_assoc _ _ _⟩
      · apply Or.inl
        have he : (t*s)*(t*r) = s*r := by
          calc
            (t*s)*(t*r) = t*(s*t)*r := by group
            _ = t*(t*s)*r := by rw [hc s hs]
            _ = s*r := by rw [← mul_assoc t t s, ht, one_mul]
        rw [he]; exact S.subgroup.mul_mem hs hr
    inv_mem' := by
      rintro u (hu | ⟨s, hs, rfl⟩)
      · exact Or.inl (S.subgroup.inv_mem hu)
      · refine Or.inr ⟨s⁻¹, S.subgroup.inv_mem hs, ?_⟩
        have hi : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht; rw [mul_inv_rev, hi, hc _ (S.subgroup.inv_mem hs)]
  }
  have hTK : T = K := le_antisymm
    ((Subgroup.closure_le K).mpr (Set.union_subset (fun _ hu => Or.inl hu) (by intro u hu; exact Or.inr ⟨1,S.subgroup.one_mem,by simpa only [mul_one] using (Set.mem_singleton_iff.mp hu)⟩)))
    (by rintro u (hu | ⟨s,hs,rfl⟩); exact Subgroup.subset_closure (Or.inl hu); exact T.mul_mem (Subgroup.subset_closure (Or.inr (Set.mem_singleton t))) (Subgroup.subset_closure (Or.inl hs)))
  have hTpauli : T ≤ pauliGroup n := by
    rw [hTK]
    rintro u (hu | ⟨s, hs, rfl⟩)
    · exact S.pauli hu
    · exact (pauliGroup n).mul_mem ⟨1, Or.inl rfl, w, by simp [t, wordUnit]⟩ (S.pauli hs)
  have hSle : S.subgroup ≤ T := by rw [hTK]; exact fun _ hu => Or.inl hu
  have htt : t ∈ T := by rw [hTK]; exact Or.inr ⟨1, S.subgroup.one_mem, (mul_one t).symm⟩
  have hTneg : (-1 : (Operator n)ˣ) ∉ T := by
    rw [hTK]
    rintro (hn' | ⟨s, hs, he⟩)
    · exact S.excludes_neg_identity hn'
    · apply hn.2
      have he' : (-1 : (Operator n)ˣ) * t = s := by
        calc
          (-1 : (Operator n)ˣ) * t = t * (-1 : (Operator n)ˣ) := neg_identity_comm t
          _ = t*(t*s) := by rw [he]
          _ = s := by rw [← mul_assoc, ht, one_mul]
      rw [he']; exact hs
  have hTab : ∀ u ∈ T, ∀ v ∈ T, u*v = v*u := by
    rw [hTK]
    rintro u (hu | ⟨s, hs, rfl⟩) v (hv | ⟨r, hr, rfl⟩)
    · exact S.abelian u hu v hv
    · calc
        u*(t*r) = (u*t)*r := (mul_assoc _ _ _).symm
        _ = (t*u)*r := by rw [← hc u hu]
        _ = t*(u*r) := mul_assoc _ _ _
        _ = t*(r*u) := by rw [S.abelian u hu r hr]
        _ = (t*r)*u := (mul_assoc _ _ _).symm
    · calc
        (t*s)*v = t*(s*v) := mul_assoc _ _ _
        _ = t*(v*s) := by rw [S.abelian s hs v hv]
        _ = (t*v)*s := (mul_assoc _ _ _).symm
        _ = (v*t)*s := by rw [hc v hv]
        _ = v*(t*s) := mul_assoc _ _ _
    · calc
        (t*s)*(t*r) = t*(s*t)*r := by group
        _ = t*(t*s)*r := by rw [hc s hs]
        _ = s*r := by rw [← mul_assoc t t s, ht, one_mul]
        _ = r*s := S.abelian s hs r hr
        _ = t*(t*r)*s := by rw [← mul_assoc t t r, ht, one_mul]
        _ = t*(r*t)*s := by rw [hc r hr]
        _ = (t*r)*(t*s) := by group
  have he := S.maximal T hTpauli hTab hTneg hSle
  exact hn.1 (he ▸ htt)
private def groupSpan {n : ℕ} (S : StabilizerGroup n) : Submodule ℂ (Operator n) := Submodule.span ℂ ((fun u : (Operator n)ˣ => (u : Operator n)) '' (S.subgroup : Set _))
def CommonEigenvector {n : ℕ} (S : StabilizerGroup n) (v : State n) : Prop := ∀ u ∈ S.subgroup, ∃ eigen : ℂ, Matrix.mulVec (u : Operator n) v = eigen • v
lemma pauli_hermitian (p : Pauli) : (pauliMatrix p).conjTranspose = pauliMatrix p := (by cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply])
lemma word_hermitian {n : ℕ} (w : (Fin n → Pauli)) : (wordOp w).conjTranspose = wordOp w := (by ext x y; simp only [wordOp, tensorOp, Matrix.of_apply, Matrix.conjTranspose_apply, star_prod]; apply Finset.prod_congr rfl; intro i _; exact congrFun (congrFun (pauli_hermitian (w i)) (x i)) (y i))
private lemma projector_in_group_span {n : ℕ} (S : StabilizerGroup n) (v : State n) (hv : v ≠ 0) (he : CommonEigenvector S v) : rankOneDensity v ∈ groupSpan S := by
  have word_comm_or_anti {n : ℕ} (v w : (Fin n → Pauli)) : wordOp v * wordOp w = wordOp w * wordOp v ∨ wordOp v * wordOp w = -(wordOp w * wordOp v) := by
    have tensor_mul {n : ℕ} (M N : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : tensorOp M * tensorOp N = tensorOp fun i => M i * N i := (by
      classical
      ext x z; simp only [tensorOp, Matrix.mul_apply, Matrix.of_apply]; simp_rw [← Finset.prod_mul_distrib]; rw [Finset.prod_univ_sum, Fintype.piFinset_univ])
    have tensor_smul {n : ℕ} (c : Fin n → ℂ) (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : tensorOp (fun i => c i • M i) = (∏ i, c i) • tensorOp M := (by ext x y; simp [tensorOp, Finset.prod_mul_distrib])
    have letter_comm (p q : Pauli) : pauliMatrix p * pauliMatrix q = ((StabilizerPairLocalUnitaryInequivalence.sgn p q : ℤ) : ℂ) • (pauliMatrix q * pauliMatrix p) := (by cases p <;> cases q <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [sgn, anticomm, pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two])
    have word_comm_sign {n : ℕ} (v w : (Fin n → Pauli)) : wordOp v * wordOp w = (∏ i, ((StabilizerPairLocalUnitaryInequivalence.sgn (v i) (w i) : ℤ) : ℂ)) • (wordOp w * wordOp v) := by
      unfold wordOp; rw [tensor_mul, tensor_mul]
      calc
        tensorOp (fun i => pauliMatrix (v i) * pauliMatrix (w i)) =
          tensorOp (fun i => ((StabilizerPairLocalUnitaryInequivalence.sgn (v i) (w i) : ℤ) : ℂ) • (pauliMatrix (w i) * pauliMatrix (v i))) :=
          congrArg tensorOp (funext fun i => letter_comm (v i) (w i))
        _ = _ := tensor_smul _ _
    have hs : (∏ i, ((StabilizerPairLocalUnitaryInequivalence.sgn (v i) (w i) : ℤ) : ℂ)) = (1 : ℂ) ∨ (∏ i, ((StabilizerPairLocalUnitaryInequivalence.sgn (v i) (w i) : ℤ) : ℂ)) = -1 := by
      apply Finset.prod_induction _ (fun c : ℂ => c = 1 ∨ c = -1)
      · intro a b ha hb; rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp
      · exact Or.inl rfl
      · intro i _; unfold sgn; split_ifs <;> simp
    rcases hs with h | h
    · exact Or.inl (by simpa [h] using word_comm_sign v w)
    · exact Or.inr (by simpa [h] using word_comm_sign v w)
  have tensor_one {n : ℕ} : tensorOp (fun _ : Fin n => (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
    classical
    ext x y; simp only [tensorOp, Matrix.of_apply, Matrix.one_apply, Fintype.prod_boole, ← funext_iff]
  have stabilizer_real_phase {n : ℕ} (S : StabilizerGroup n) {u : (Operator n)ˣ} (hu : u ∈ S.subgroup) {c : ℂ} {w : (Fin n → Pauli)} (hc : Phase c) (hw : (u : Operator n) = c • wordOp w) : c = 1 ∨ c = -1 := by
    have tensor_mul {n : ℕ} (M N : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : tensorOp M * tensorOp N = tensorOp fun i => M i * N i := (by
      classical
      ext x z; simp only [tensorOp, Matrix.mul_apply, Matrix.of_apply]; simp_rw [← Finset.prod_mul_distrib]; rw [Finset.prod_univ_sum, Fintype.piFinset_univ])
    have pauli_sq (p : Pauli) : pauliMatrix p * pauliMatrix p = 1 := (by cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two])
    have word_sq {n : ℕ} (w : (Fin n → Pauli)) : wordOp w * wordOp w = 1 := (by unfold wordOp; rw [tensor_mul]; simp_rw [pauli_sq]; exact tensor_one)
    rcases hc with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    all_goals
      exfalso
      have he : u*u = (-1 : (Operator n)ˣ) := (by apply Units.ext; simp [hw, h, smul_mul_smul, word_sq, Algebra.algebraMap_eq_smul_one, smul_smul, Complex.I_mul_I])
      exact S.excludes_neg_identity (he ▸ S.subgroup.mul_mem hu hu)
  have common_projector_comm {n : ℕ} (S : StabilizerGroup n) (v : State n) (hv : v ≠ 0) (he : CommonEigenvector S v) : ∀ u ∈ S.subgroup, (u : Operator n)*rankOneDensity v = rankOneDensity v*(u : Operator n) := by
    have tensor_mul {n : ℕ} (M N : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : tensorOp M * tensorOp N = tensorOp fun i => M i * N i := (by
      classical
      ext x z; simp only [tensorOp, Matrix.mul_apply, Matrix.of_apply]; simp_rw [← Finset.prod_mul_distrib]; rw [Finset.prod_univ_sum, Fintype.piFinset_univ])
    have pauli_sq (p : Pauli) : pauliMatrix p * pauliMatrix p = 1 := (by cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two])
    have word_sq {n : ℕ} (w : (Fin n → Pauli)) : wordOp w * wordOp w = 1 := (by unfold wordOp; rw [tensor_mul]; simp_rw [pauli_sq]; exact tensor_one)
    have stabilizer_involution {n : ℕ} (S : StabilizerGroup n) {u : (Operator n)ˣ} (hu : u ∈ S.subgroup) : u*u = 1 := (by obtain ⟨c, hc, w, hw⟩ := S.pauli hu; obtain h | h := stabilizer_real_phase S hu hc hw; all_goals apply Units.ext; simp [hw, h, word_sq])
    have stabilizer_hermitian {n : ℕ} (S : StabilizerGroup n) {u : (Operator n)ˣ} (hu : u ∈ S.subgroup) : (u : Operator n).conjTranspose = (u : Operator n) := (by obtain ⟨c, hc, w, hw⟩ := S.pauli hu; obtain h | h := stabilizer_real_phase S hu hc hw; all_goals simp [hw, h, word_hermitian])
    classical
    intro u hu
    obtain ⟨c, hc⟩ := he u hu
    have hsq : (u : Operator n)*(u : Operator n) = 1 := congrArg Units.val (stabilizer_involution S hu)
    have hcc : c*c = 1 := (by have ht : (c*c) • v = (1 : ℂ) • v := (by rw [one_smul, ← smul_smul, ← hc, ← Matrix.mulVec_smul, ← hc, Matrix.mulVec_mulVec, hsq, Matrix.one_mulVec]); exact (smul_left_injective ℂ hv) ht)
    have hreal : star c = c := (by have h : c = 1 ∨ c = -1 := (by rw [← pow_two] at hcc; exact sq_eq_one_iff.mp hcc); rcases h with rfl | rfl <;> simp)
    have hs : Matrix.vecMul (star v) (u : Operator n) = c • star v := (by have hh := congrArg star hc; rw [Matrix.star_mulVec, stabilizer_hermitian S hu] at hh; simpa [hreal] using hh)
    unfold rankOneDensity; rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hc, hs]; ext x y; simp [Matrix.vecMulVec, mul_assoc, mul_left_comm]
  have tensor_mul {n : ℕ} (M N : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : tensorOp M * tensorOp N = tensorOp fun i => M i * N i := (by
    classical
    ext x z; simp only [tensorOp, Matrix.mul_apply, Matrix.of_apply]; simp_rw [← Finset.prod_mul_distrib]; rw [Finset.prod_univ_sum, Fintype.piFinset_univ])
  have pauli_sq (p : Pauli) : pauliMatrix p * pauliMatrix p = 1 := (by cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two])
  have word_sq {n : ℕ} (w : (Fin n → Pauli)) : wordOp w * wordOp w = 1 := (by unfold wordOp; rw [tensor_mul]; simp_rw [pauli_sq]; exact tensor_one)
  have stabilizer_involution {n : ℕ} (S : StabilizerGroup n) {u : (Operator n)ˣ} (hu : u ∈ S.subgroup) : u*u = 1 := (by obtain ⟨c, hc, w, hw⟩ := S.pauli hu; obtain h | h := stabilizer_real_phase S hu hc hw; all_goals apply Units.ext; simp [hw, h, word_sq])
  have unit_word_comm_or_anti {n : ℕ} (w : (Fin n → Pauli)) {u : (Operator n)ˣ} (hu : u ∈ pauliGroup n) : wordOp w*(u : Operator n) = (u : Operator n)*wordOp w ∨ (u : Operator n)*wordOp w = -(wordOp w*(u : Operator n)) := by
    obtain ⟨c, _, z, hz⟩ := hu
    obtain h | h := word_comm_or_anti z w
    · exact Or.inl (by rw [hz, Matrix.mul_smul, Matrix.smul_mul, h])
    · exact Or.inr (by rw [hz, Matrix.mul_smul, Matrix.smul_mul, h, smul_neg])
  have commutant_zero {n : ℕ} (A : Operator n) (w : (Fin n → Pauli)) (u : (Operator n)ˣ) (hsq : (u : Operator n)*(u : Operator n) = 1) (hcomm : A*(u : Operator n) = (u : Operator n)*A) (hanti : (u : Operator n)*wordOp w = -(wordOp w*(u : Operator n))) : Matrix.trace (wordOp w*A) = 0 := by
    have hm : (u : Operator n)*(wordOp w*A)*(u : Operator n) = -(wordOp w*A) := by
      calc
        (u : Operator n)*(wordOp w*A)*(u : Operator n) =
          ((u : Operator n)*wordOp w)*(A*(u : Operator n)) := by noncomm_ring
        _ = -(wordOp w*(u : Operator n))*((u : Operator n)*A) := by rw [hanti, hcomm]
        _ = -(wordOp w*((u : Operator n)*(u : Operator n))*A) := by noncomm_ring
        _ = -(wordOp w*A) := by rw [hsq, mul_one]
    have ht : Matrix.trace ((u : Operator n)*(wordOp w*A)*(u : Operator n)) = Matrix.trace (wordOp w*A) := (by rw [Matrix.trace_mul_cycle, hsq, one_mul])
    rw [hm, Matrix.trace_neg] at ht; exact neg_eq_self.mp ht
  classical
  rw [word_expansion (rankOneDensity v)]; apply Submodule.sum_mem; intro w _
  by_cases hz : Matrix.trace (wordOp w*rankOneDensity v) = 0
  · simp [hz]
  · have hc : ∀ u ∈ S.subgroup, wordUnit w*u = u*wordUnit w := by
      intro u hu; apply Units.ext
      obtain h | h := unit_word_comm_or_anti w (S.pauli hu)
      · exact h
      · exfalso
        apply hz; exact commutant_zero (rankOneDensity v) w u
          (congrArg Units.val (stabilizer_involution S hu))
          (common_projector_comm S v hv he u hu).symm h
    obtain h | h := maximal_word S w hc
    · apply Submodule.smul_mem
      exact Submodule.subset_span ⟨wordUnit w, h, rfl⟩
    · have hh : -(wordOp w) ∈ groupSpan S := by
        apply Submodule.subset_span; exact ⟨(-1 : (Operator n)ˣ)*wordUnit w, h, by simp [ Algebra.algebraMap_eq_smul_one, wordUnit]⟩
      have hw : wordOp w ∈ groupSpan S := (by simpa using (groupSpan S).neg_mem hh)
      exact (groupSpan S).smul_mem _ hw
private def restrictData {n m : ℕ} (w : (Fin (n+m) → Pauli)) : (Fin n → Pauli) := fun i => w (Fin.castAdd m i)
private def restrictAncilla {n m : ℕ} (w : (Fin (n+m) → Pauli)) : (Fin m → Pauli) := fun j => w (Fin.natAdd n j)
abbrev UnitState (m : ℕ) := {ψ : EuclideanSpace ℂ ((Fin m → Fin 2)) // ‖ψ‖ = 1}
/-- The frame inserting a normalized ancilla next to the data register. -/
def ancillaEmbedding {n m : ℕ} (ψ : UnitState m) : Matrix (Fin (n+m) → Fin 2) (Fin n → Fin 2) ℂ :=
  (Matrix.kronecker (1 : Operator n) (Matrix.replicateCol Unit ψ.val)).submatrix
    (Fin.appendEquiv n m).symm (fun x => (x, ()))
private def expectation {m : ℕ} (w : (Fin m → Pauli)) (ψ : UnitState m) : ℂ := ∑ a, ∑ b, star (ψ.val a)*wordOp w a b*ψ.val b
structure StabilizerBasis (n m : ℕ) where
  group : StabilizerGroup (n+m)
  vectors : (Fin (n+m) → Fin 2) → State (n+m)
  orthonormal : ∀ i j, (∑ x, star (vectors i x)*vectors j x) = if i = j then 1 else 0
  common_eigen : ∀ i, CommonEigenvector group (vectors i)
  spans : Submodule.span ℂ (Set.range vectors) = ⊤
def mu {n m : ℕ} (ψ : UnitState m) (v : State (n+m)) : Operator n := IsometricCompression.compress (ancillaEmbedding ψ) (rankOneDensity v)
def smu {n m : ℕ} (ψ : UnitState m) (B : StabilizerBasis n m) : ℕ := Module.finrank ℂ (Submodule.span ℂ (Set.range (fun b => mu ψ (B.vectors b))))
private structure PauliRepresentation {n : ℕ} (u : (Operator n)ˣ) where
  phase : ℂ
  phase_mem : Phase phase
  word : (Fin n → Pauli)
  equality : (u : Operator n) = phase • wordOp word
private def representation {n : ℕ} (u : (Operator n)ˣ) (hu : u ∈ pauliGroup n) : PauliRepresentation u := Classical.choice (by obtain ⟨c, hc, w, hw⟩ := hu; exact ⟨⟨c, hc, w, hw⟩⟩)
def supportedPauliGroup (n : ℕ) (J : Set (Fin n)) : Subgroup (Operator n)ˣ := by
  have tensor_one {n : ℕ} : tensorOp (fun _ : Fin n => (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
    classical
    ext x y; simp only [tensorOp, Matrix.of_apply, Matrix.one_apply, Fintype.prod_boole, ← funext_iff]
  have phase_ne_zero {c : ℂ} (h : Phase c) : c ≠ 0 := (by rcases h with rfl | rfl | rfl | rfl <;> simp)
  have phase_mul {c d : ℂ} (hc : Phase c) (hd : Phase d) : Phase (c*d) := (by rcases hc with rfl | rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl | rfl <;> simp [Phase, Complex.I_mul_I])
  have phase_inv {c : ℂ} (h : Phase c) : Phase c⁻¹ := (by rcases h with rfl | rfl | rfl | rfl <;> simp [Phase, Complex.inv_I])
  have phase_prod {n : ℕ} (c : Fin n → ℂ) (h : ∀ i, Phase (c i)) : Phase (∏ i, c i) := (by exact Finset.prod_induction _ _ (fun _ _ => phase_mul) (by simp [Phase]) (fun i _ => h i))
  have tensor_mul {n : ℕ} (M N : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : tensorOp M * tensorOp N = tensorOp fun i => M i * N i := (by
    classical
    ext x z; simp only [tensorOp, Matrix.mul_apply, Matrix.of_apply]; simp_rw [← Finset.prod_mul_distrib]; rw [Finset.prod_univ_sum, Fintype.piFinset_univ])
  have tensor_smul {n : ℕ} (c : Fin n → ℂ) (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : tensorOp (fun i => c i • M i) = (∏ i, c i) • tensorOp M := (by ext x y; simp [tensorOp, Finset.prod_mul_distrib])
  have letter_phase (p q : Pauli) : Phase (letterPhase p q) := (by cases p <;> cases q <;> simp [letterPhase, Phase])
  have letter_mul (p q : Pauli) : pauliMatrix p * pauliMatrix q = letterPhase p q • pauliMatrix (letterProduct p q) := (by cases p <;> cases q <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [letterPhase, letterProduct, pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two])
  have word_one {n : ℕ} : wordOp (fun _ : Fin n => Pauli.I) = 1 := tensor_one
  have word_mul {n : ℕ} (v w : (Fin n → Pauli)) : wordOp v * wordOp w = (∏ i, letterPhase (v i) (w i)) • wordOp (fun i => letterProduct (v i) (w i)) := (by unfold wordOp; rw [tensor_mul]; simp_rw [letter_mul]; exact tensor_smul _ _)
  exact {
    carrier := {u | ∃ c : ℂ, Phase c ∧ ∃ w : (Fin n → Pauli),
      (u : Operator n) = c • wordOp w ∧ ∀ i ∉ J, w i = Pauli.I}
    one_mem' := ⟨1, Or.inl rfl, fun _ => Pauli.I, by simp [word_one], by simp⟩
    mul_mem' := by
      rintro u v ⟨c, hc, w, hw, hs⟩ ⟨d, hd, z, hz, ht⟩; refine ⟨c*d*(∏ i, letterPhase (w i) (z i)),
        phase_mul (phase_mul hc hd) (phase_prod _ (fun i => letter_phase _ _)),
        (fun i => letterProduct (w i) (z i)), ?_, ?_⟩
      · simp only [Units.val_mul, hw, hz, smul_mul_smul, word_mul, smul_smul]
      · intro i hi; simp [hs i hi, ht i hi, letterProduct]
    inv_mem' := by rintro u ⟨c, hc, w, hw, hs⟩; refine ⟨c⁻¹, phase_inv hc, w, ?_, hs⟩; have hu : u = Units.map (algebraMap ℂ (Operator n)).toMonoidHom (Units.mk0 c (phase_ne_zero hc))*wordUnit w := (by apply Units.ext; simp [Algebra.algebraMap_eq_smul_one, wordUnit, hw]); rw [hu, mul_inv_rev]; simp [wordUnit, Algebra.algebraMap_eq_smul_one]
  }
def dataSubgroup {n m : ℕ} (S : StabilizerGroup (n+m)) : Subgroup (Operator (n+m))ˣ := S.subgroup ⊓ supportedPauliGroup (n+m) {i | i.val < n}
def ancillaSubgroup {n m : ℕ} (S : StabilizerGroup (n+m)) : Subgroup (Operator (n+m))ˣ := S.subgroup ⊓ supportedPauliGroup (n+m) {i | n ≤ i.val}
def dimData {n m : ℕ} (S : StabilizerGroup (n+m)) : ℕ := Nat.log 2 (Nat.card (dataSubgroup S))
def dimAncilla {n m : ℕ} (S : StabilizerGroup (n+m)) : ℕ := Nat.log 2 (Nat.card (ancillaSubgroup S))
def entanglementP {n m : ℕ} (S : StabilizerGroup (n+m)) : ℚ := ((n : ℚ)+(m : ℚ)-(dimData S : ℚ)-(dimAncilla S : ℚ))/2
def MaximallyEntangled {n m : ℕ} (B : StabilizerBasis n m) : Prop := entanglementP B.group = ((min n m : ℕ) : ℚ)
def claim : Prop := ∀ (n m : ℕ) (ψ : UnitState m), ∃ B : StabilizerBasis n m, MaximallyEntangled B ∧ ∀ B' : StabilizerBasis n m, smu ψ B' ≤ smu ψ B
private lemma ancilla_injective {n : ℕ} (S : StabilizerGroup (n+n)) (hmax : entanglementP S = n) : Function.Injective (fun u : S.subgroup => restrictAncilla (representation u.val (S.pauli u.property)).word) := by
  letI (k : ℕ) : Finite (pauliGroup k) := by
    classical
    have hf (c : ℂ) := Set.finite_range (fun w : Fin k → Pauli => c • wordOp w)
    apply (Set.finite_range_iff (show Function.Injective (fun u : pauliGroup k => (u.val : Operator k)) from fun _ _ h => Subtype.ext (Units.ext h))).mp
    exact (((hf 1).union (hf (-1))).union ((hf Complex.I).union (hf (-Complex.I)))).subset (by rintro _ ⟨u,rfl⟩; dsimp only; obtain ⟨c,hc,w,hw⟩ := u.property; rcases hc with rfl | rfl | rfl | rfl <;> rw [hw] <;> simp only [Set.mem_union, Set.mem_range] <;> aesop)
  have tensor_one {n : ℕ} : tensorOp (fun _ : Fin n => (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
    classical
    ext x y; simp only [tensorOp, Matrix.of_apply, Matrix.one_apply, Fintype.prod_boole, ← funext_iff]
  have stabilizer_real_phase {n : ℕ} (S : StabilizerGroup n) {u : (Operator n)ˣ} (hu : u ∈ S.subgroup) {c : ℂ} {w : (Fin n → Pauli)} (hc : Phase c) (hw : (u : Operator n) = c • wordOp w) : c = 1 ∨ c = -1 := by
    have tensor_mul {n : ℕ} (M N : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : tensorOp M * tensorOp N = tensorOp fun i => M i * N i := (by
      classical
      ext x z; simp only [tensorOp, Matrix.mul_apply, Matrix.of_apply]; simp_rw [← Finset.prod_mul_distrib]; rw [Finset.prod_univ_sum, Fintype.piFinset_univ])
    have pauli_sq (p : Pauli) : pauliMatrix p * pauliMatrix p = 1 := (by cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two])
    have word_sq {n : ℕ} (w : (Fin n → Pauli)) : wordOp w * wordOp w = 1 := (by unfold wordOp; rw [tensor_mul]; simp_rw [pauli_sq]; exact tensor_one)
    rcases hc with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    all_goals
      exfalso
      have he : u*u = (-1 : (Operator n)ˣ) := (by apply Units.ext; simp [hw, h, smul_mul_smul, word_sq, Algebra.algebraMap_eq_smul_one, smul_smul, Complex.I_mul_I])
      exact S.excludes_neg_identity (he ▸ S.subgroup.mul_mem hu hu)
  have phase_mul {c d : ℂ} (hc : Phase c) (hd : Phase d) : Phase (c*d) := (by rcases hc with rfl | rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl | rfl <;> simp [Phase, Complex.I_mul_I])
  have phase_prod {n : ℕ} (c : Fin n → ℂ) (h : ∀ i, Phase (c i)) : Phase (∏ i, c i) := (by exact Finset.prod_induction _ _ (fun _ _ => phase_mul) (by simp [Phase]) (fun i _ => h i))
  have tensor_mul {n : ℕ} (M N : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : tensorOp M * tensorOp N = tensorOp fun i => M i * N i := (by
    classical
    ext x z; simp only [tensorOp, Matrix.mul_apply, Matrix.of_apply]; simp_rw [← Finset.prod_mul_distrib]; rw [Finset.prod_univ_sum, Fintype.piFinset_univ])
  have tensor_smul {n : ℕ} (c : Fin n → ℂ) (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : tensorOp (fun i => c i • M i) = (∏ i, c i) • tensorOp M := (by ext x y; simp [tensorOp, Finset.prod_mul_distrib])
  have pauli_sq (p : Pauli) : pauliMatrix p * pauliMatrix p = 1 := (by cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two])
  have letter_phase (p q : Pauli) : Phase (letterPhase p q) := (by cases p <;> cases q <;> simp [letterPhase, Phase])
  have letter_mul (p q : Pauli) : pauliMatrix p * pauliMatrix q = letterPhase p q • pauliMatrix (letterProduct p q) := (by cases p <;> cases q <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [letterPhase, letterProduct, pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two])
  have word_sq {n : ℕ} (w : (Fin n → Pauli)) : wordOp w * wordOp w = 1 := (by unfold wordOp; rw [tensor_mul]; simp_rw [pauli_sq]; exact tensor_one)
  have word_mul {n : ℕ} (v w : (Fin n → Pauli)) : wordOp v * wordOp w = (∏ i, letterPhase (v i) (w i)) • wordOp (fun i => letterProduct (v i) (w i)) := (by unfold wordOp; rw [tensor_mul]; simp_rw [letter_mul]; exact tensor_smul _ _)
  have stabilizer_involution {n : ℕ} (S : StabilizerGroup n) {u : (Operator n)ˣ} (hu : u ∈ S.subgroup) : u*u = 1 := (by obtain ⟨c, hc, w, hw⟩ := S.pauli hu; obtain h | h := stabilizer_real_phase S hu hc hw; all_goals apply Units.ext; simp [hw, h, word_sq])
  have exact_half_balance (n a b : ℕ) : ((n : ℚ)+(n : ℚ)-(a : ℚ)-(b : ℚ))/2 = (n : ℚ) ↔ a = 0 ∧ b = 0 := by
    constructor
    · intro h
      have ha : 0 ≤ (a : ℚ) := Nat.cast_nonneg a
      have hb : 0 ≤ (b : ℚ) := Nat.cast_nonneg b
      have hza : (a : ℚ) = 0 := (by linarith)
      have hzb : (b : ℚ) = 0 := (by linarith)
      exact ⟨Nat.cast_eq_zero.mp hza,Nat.cast_eq_zero.mp hzb⟩
    · rintro ⟨rfl,rfl⟩
      push_cast
      ring
  have log_card_zero_iff {G : Type} [Group G] (H : Subgroup G) [Finite H] : Nat.log 2 (Nat.card H) = 0 ↔ ∀ u ∈ H, u = 1 := by
    rw [Nat.log_eq_zero_iff]
    constructor
    · intro h
      have hp : 0 < Nat.card H := Nat.card_pos
      have hc : Nat.card H = 1 := (by omega)
      have hi := (Nat.card_eq_one_iff_unique.mp hc).1
      intro u hu; exact congrArg Subtype.val (@Subsingleton.elim H hi ⟨u,hu⟩ 1)
    · intro h
      have hi : Subsingleton H := ⟨fun u v => Subtype.ext ((h u u.property).trans (h v v.property).symm)⟩
      have hc := Nat.card_eq_one_iff_unique.mpr (show Subsingleton H ∧ Nonempty H from ⟨hi,inferInstance⟩)
      exact Or.inl (by omega)
  have max_entangled_equal_iff {n : ℕ} (S : StabilizerGroup (n+n)) : entanglementP S = n ↔ (∀ u ∈ dataSubgroup S, u = 1) ∧ (∀ u ∈ ancillaSubgroup S, u = 1) := (by letI : Finite S.subgroup := Finite.of_injective (fun u : S.subgroup => (⟨u.val, S.pauli u.property⟩ : pauliGroup (n+n))) (fun _ _ h => Subtype.ext (congrArg (fun z : pauliGroup (n+n) => z.val) h)); letI : Finite (dataSubgroup S) := Finite.of_injective (fun u : dataSubgroup S => (⟨u.val, u.property.1⟩ : S.subgroup)) (fun _ _ h => Subtype.ext (congrArg (fun z : S.subgroup => z.val) h)); letI : Finite (ancillaSubgroup S) := Finite.of_injective (fun u : ancillaSubgroup S => (⟨u.val, u.property.1⟩ : S.subgroup)) (fun _ _ h => Subtype.ext (congrArg (fun z : S.subgroup => z.val) h)); have hdim : entanglementP S = n ↔ dimData S = 0 ∧ dimAncilla S = 0 := exact_half_balance n (dimData S) (dimAncilla S); rw [hdim, dimData, dimAncilla, log_card_zero_iff (dataSubgroup S), log_card_zero_iff (ancillaSubgroup S)])
  have letter_product_self (p : Pauli) : letterProduct p p = Pauli.I := (by cases p <;> rfl)
  intro u v h
  let r := representation u.val (S.pauli u.property)
  let t := representation v.val (S.pauli v.property)
  have he : ∀ i : Fin n, r.word (Fin.natAdd n i) = t.word (Fin.natAdd n i) := congrFun h
  have huv : u.val*v.val ∈ dataSubgroup S := by
    refine ⟨S.subgroup.mul_mem u.property v.property, ?_⟩; refine ⟨r.phase*t.phase*(∏ i, letterPhase (r.word i) (t.word i)),
      phase_mul (phase_mul r.phase_mem t.phase_mem) (phase_prod _ (fun i => letter_phase _ _)),
      (fun i => letterProduct (r.word i) (t.word i)), ?_, ?_⟩
    · simp [r.equality, t.equality, smul_mul_smul, word_mul, smul_smul, mul_assoc, mul_left_comm]
    · intro i hi
      have hni : n ≤ i.val := (by simpa using hi)
      let j : Fin n := ⟨i.val-n, by omega⟩
      have hij : i = Fin.natAdd n j := (by ext; simp [j]; omega)
      rw [hij]; dsimp only; rw [he j, letter_product_self]
  have hprod := (max_entangled_equal_iff S).mp hmax |>.1 _ huv
  apply Subtype.ext
  calc
    u.val = u.val*(v.val*v.val) := by rw [stabilizer_involution S v.property, mul_one]
    _ = v.val := by rw [← mul_assoc, hprod, one_mul]
private def compressLinear {n m : ℕ} (ψ : UnitState m) : Operator (n+m) →ₗ[ℂ] Operator n :=
  { (_root_.mulRightLinearMap (Fin n → Fin 2) ℂ (ancillaEmbedding ψ)).comp
      (_root_.mulLeftLinearMap (Fin (n+m) → Fin 2) ℂ (ancillaEmbedding ψ).conjTranspose) with toFun := fun A => IsometricCompression.compress (ancillaEmbedding ψ) A }
private lemma maximal_entangled_support_bound {n : ℕ} (ψ : UnitState n) (B : StabilizerBasis n n) (hmax : MaximallyEntangled B) : smu ψ B ≤ Nat.card {w : (Fin n → Pauli) // expectation w ψ ≠ 0} := by
  letI (k : ℕ) : Finite (pauliGroup k) := by
    classical
    have hf (c : ℂ) := Set.finite_range (fun w : Fin k → Pauli => c • wordOp w)
    apply (Set.finite_range_iff (show Function.Injective (fun u : pauliGroup k => (u.val : Operator k)) from fun _ _ h => Subtype.ext (Units.ext h))).mp
    exact (((hf 1).union (hf (-1))).union ((hf Complex.I).union (hf (-Complex.I)))).subset (by rintro _ ⟨u,rfl⟩; dsimp only; obtain ⟨c,hc,w,hw⟩ := u.property; rcases hc with rfl | rfl | rfl | rfl <;> rw [hw] <;> simp only [Set.mem_union, Set.mem_range] <;> aesop)
  have word_split {n m : ℕ} (w : (Fin (n+m) → Pauli)) (d e : (Fin n → Fin 2)) (a b : (Fin m → Fin 2)) : wordOp w (Fin.addCases d a) (Fin.addCases e b) = wordOp (restrictData w) d e * wordOp (restrictAncilla w) a b := (by simp only [wordOp, tensorOp, Matrix.of_apply]; rw [Fin.prod_univ_add]; simp [Fin.addCases, restrictData, restrictAncilla])
  have compress_pauli {n m : ℕ} (w : (Fin (n+m) → Pauli)) (c : ℂ) (ψ : UnitState m) : IsometricCompression.compress (ancillaEmbedding ψ) (c • wordOp w) = (c*expectation (restrictAncilla w) ψ) • wordOp (restrictData w) := by
    have compression_entry (A : Operator (n+m)) (x y : Fin n → Fin 2) : IsometricCompression.compress (ancillaEmbedding ψ) A x y = ∑ a, ∑ b, star (ψ.val a)*A (Fin.addCases x a) (Fin.addCases y b)*ψ.val b := by classical
      simp only [IsometricCompression.compress, Matrix.mul_apply, Matrix.conjTranspose_apply]; simp_rw [← (Fin.appendEquiv (α := Fin 2) n m).sum_comp]; simp only [Fintype.sum_prod_type, ancillaEmbedding, Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Matrix.kronecker, Matrix.one_apply, Matrix.replicateCol_apply, Equiv.symm_apply_apply]; simp [Fin.appendEquiv, Fin.append, Finset.sum_mul, apply_ite, ite_mul, Finset.sum_ite_irrel] <;> rw [Finset.sum_comm]
    ext x y; simp only [compression_entry, Matrix.smul_apply, smul_eq_mul, word_split, expectation]
    calc
      _ = ∑ a, (c*wordOp (restrictData w) x y)*
          ∑ b, star (ψ.val a)*wordOp (restrictAncilla w) a b*ψ.val b := by
        apply Finset.sum_congr rfl; intro a _; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
      _ = (c*wordOp (restrictData w) x y)*
          ∑ a, ∑ b, star (ψ.val a)*wordOp (restrictAncilla w) a b*ψ.val b :=
        (Finset.mul_sum _ _ _).symm
      _ = _ := by ring
  have stabilizer_vector_nonzero {n m : ℕ} (B : StabilizerBasis n m) (i : (Fin (n+m) → Fin 2)) : B.vectors i ≠ 0 := (by intro h; have hh := B.orthonormal i i; simp [h] at hh)
  classical
  letI : Finite B.group.subgroup := Finite.of_injective (fun u : B.group.subgroup => (⟨u.val, B.group.pauli u.property⟩ : pauliGroup (n+n))) (fun _ _ h => Subtype.ext (congrArg (fun z : pauliGroup (n+n) => z.val) h))
  let R (u : B.group.subgroup) := representation u.val (B.group.pauli u.property)
  let G := {u : B.group.subgroup // expectation (restrictAncilla (R u).word) ψ ≠ 0}
  letI : Fintype G := Fintype.ofFinite G
  let f : G → Operator n := fun u => wordOp (restrictData (R u.val).word)
  let V := Submodule.span ℂ (Set.range f)
  have hc : ∀ A ∈ groupSpan B.group, IsometricCompression.compress (ancillaEmbedding ψ) A ∈ V := by
    intro A hA
    induction hA using Submodule.span_induction with
    | mem A hA =>
      obtain ⟨u, hu, rfl⟩ := hA
      let r := R (⟨u,hu⟩ : B.group.subgroup)
      change IsometricCompression.compress (ancillaEmbedding ψ) (u : Operator (n+n)) ∈ V
      have hr : (u : Operator (n+n)) = r.phase • wordOp r.word := r.equality
      rw [hr, compress_pauli]
      by_cases hz : expectation (restrictAncilla r.word) ψ = 0
      · simp [hz]
      · apply V.smul_mem
        exact Submodule.subset_span ⟨⟨⟨u,hu⟩, hz⟩, rfl⟩
    | zero =>
      change (compressLinear ψ) 0 ∈ V; rw [map_zero]; exact V.zero_mem
    | add A C _ _ hA hC =>
      change (compressLinear ψ) (A+C) ∈ V; rw [map_add]; exact V.add_mem hA hC
    | smul c A _ hA =>
      change (compressLinear ψ) (c • A) ∈ V; rw [map_smul]; exact V.smul_mem c hA
  have hspan : Submodule.span ℂ (Set.range (fun b => mu ψ (B.vectors b))) ≤ V := (by apply Submodule.span_le.mpr; rintro A ⟨b,rfl⟩; exact hc _ (projector_in_group_span B.group (B.vectors b) (stabilizer_vector_nonzero B b) (B.common_eigen b)))
  have hdim : smu ψ B ≤ Nat.card G := by
    calc
      smu ψ B ≤ Module.finrank ℂ V := Submodule.finrank_mono hspan
      _ ≤ Fintype.card G := finrank_range_le_card f
      _ = Nat.card G := Nat.card_eq_fintype_card.symm
  have hm : entanglementP B.group = n := (by simpa [MaximallyEntangled] using hmax)
  let q : G → {w : (Fin n → Pauli) // expectation w ψ ≠ 0} := fun u => ⟨restrictAncilla (R u.val).word, u.property⟩
  have hi : Function.Injective q := (by intro u v h; apply Subtype.ext; apply ancilla_injective B.group hm; exact congrArg (fun z : {w : (Fin n → Pauli) // expectation w ψ ≠ 0} => z.val) h)
  exact hdim.trans (Nat.card_le_card_of_injective q hi)
private def zLetter (b : Fin 2) : Pauli := if b = 0 then .I else .Z
private def zWord {n : ℕ} (b : (Fin n → Fin 2)) : (Fin n → Pauli) := fun i => zLetter (b i)
private def standardSubgroup (n : ℕ) : Subgroup (Operator n)ˣ := by
  have tensor_one {n : ℕ} : tensorOp (fun _ : Fin n => (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
    classical
    ext x y; simp only [tensorOp, Matrix.of_apply, Matrix.one_apply, Fintype.prod_boole, ← funext_iff]
  have tensor_mul {n : ℕ} (M N : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : tensorOp M * tensorOp N = tensorOp fun i => M i * N i := (by
    classical
    ext x z; simp only [tensorOp, Matrix.mul_apply, Matrix.of_apply]; simp_rw [← Finset.prod_mul_distrib]; rw [Finset.prod_univ_sum, Fintype.piFinset_univ])
  have pauli_sq (p : Pauli) : pauliMatrix p * pauliMatrix p = 1 := (by cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two])
  have word_one {n : ℕ} : wordOp (fun _ : Fin n => Pauli.I) = 1 := tensor_one
  have word_sq {n : ℕ} (w : (Fin n → Pauli)) : wordOp w * wordOp w = 1 := (by unfold wordOp; rw [tensor_mul]; simp_rw [pauli_sq]; exact tensor_one)
  have z_letter_mul (a b : Fin 2) : pauliMatrix (zLetter a)*pauliMatrix (zLetter b) = pauliMatrix (zLetter (a+b)) := (by fin_cases a <;> fin_cases b <;> simp [zLetter, pauliMatrix]; exact pauli_sq .Z)
  have z_word_mul {n : ℕ} (a b : (Fin n → Fin 2)) : wordUnit (zWord a)*wordUnit (zWord b) = wordUnit (zWord (a+b)) := by
    apply Units.ext; change tensorOp (fun i => pauliMatrix (zLetter (a i))) *
      tensorOp (fun i => pauliMatrix (zLetter (b i))) =
      tensorOp (fun i => pauliMatrix (zLetter (a i+b i)))
    rw [tensor_mul]; exact congrArg tensorOp (funext fun i => z_letter_mul (a i) (b i))
  have z_word_zero {n : ℕ} : wordUnit (zWord (0 : (Fin n → Fin 2))) = 1 := (by apply Units.ext; exact word_one)
  exact {
    carrier := {u | ∃ b : (Fin n → Fin 2), u = wordUnit (zWord b)}
    one_mem' := ⟨0,z_word_zero.symm⟩
    mul_mem' := by rintro u v ⟨a,rfl⟩ ⟨b,rfl⟩; exact ⟨a+b,z_word_mul a b⟩
    inv_mem' := by rintro u ⟨a,rfl⟩; exact ⟨a, inv_eq_of_mul_eq_one_left (Units.ext (word_sq (zWord a)))⟩
  }
private def localZ {n : ℕ} (i : Fin n) : (Fin n → Pauli) := fun j => if j = i then .Z else .I
private lemma standard_maximal (n : ℕ) (T : Subgroup (Operator n)ˣ) (hp : T ≤ pauliGroup n) (hab : ∀ u ∈ T, ∀ v ∈ T, u*v = v*u) (hn : (-1 : (Operator n)ˣ) ∉ T) (hle : standardSubgroup n ≤ T) : T = standardSubgroup n := by
  have tensor_one {n : ℕ} : tensorOp (fun _ : Fin n => (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
    classical
    ext x y; simp only [tensorOp, Matrix.of_apply, Matrix.one_apply, Fintype.prod_boole, ← funext_iff]
  have localZ_forces_z {n : ℕ} (w : (Fin n → Pauli)) (i : Fin n) (h : wordOp w*wordOp (localZ i) = wordOp (localZ i)*wordOp w) : w i = .I ∨ w i = .Z := by
    have tensor_mul {n : ℕ} (M N : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : tensorOp M * tensorOp N = tensorOp fun i => M i * N i := (by
      classical
      ext x z; simp only [tensorOp, Matrix.mul_apply, Matrix.of_apply]; simp_rw [← Finset.prod_mul_distrib]; rw [Finset.prod_univ_sum, Fintype.piFinset_univ])
    have tensor_smul {n : ℕ} (c : Fin n → ℂ) (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : tensorOp (fun i => c i • M i) = (∏ i, c i) • tensorOp M := (by ext x y; simp [tensorOp, Finset.prod_mul_distrib])
    have letter_comm (p q : Pauli) : pauliMatrix p * pauliMatrix q = ((StabilizerPairLocalUnitaryInequivalence.sgn p q : ℤ) : ℂ) • (pauliMatrix q * pauliMatrix p) := (by cases p <;> cases q <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [sgn, anticomm, pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two])
    have word_comm_sign {n : ℕ} (v w : (Fin n → Pauli)) : wordOp v * wordOp w = (∏ i, ((StabilizerPairLocalUnitaryInequivalence.sgn (v i) (w i) : ℤ) : ℂ)) • (wordOp w * wordOp v) := by
      unfold wordOp; rw [tensor_mul, tensor_mul]
      calc
        tensorOp (fun i => pauliMatrix (v i) * pauliMatrix (w i)) =
          tensorOp (fun i => ((StabilizerPairLocalUnitaryInequivalence.sgn (v i) (w i) : ℤ) : ℂ) • (pauliMatrix (w i) * pauliMatrix (v i))) :=
          congrArg tensorOp (funext fun i => letter_comm (v i) (w i))
        _ = _ := tensor_smul _ _
    have localZ_sign {n : ℕ} (w : (Fin n → Pauli)) (i : Fin n) : (∏ j, ((StabilizerPairLocalUnitaryInequivalence.sgn (w j) (localZ i j) : ℤ) : ℂ)) = ((StabilizerPairLocalUnitaryInequivalence.sgn (w i) .Z : ℤ) : ℂ) := by
      classical
      rw [Finset.prod_eq_single i]
      · simp [localZ]
      · intro j _ hji; cases w j <;> simp [localZ, hji, sgn, anticomm]
      · simp
    have hc := word_comm_sign w (localZ i)
    rw [localZ_sign] at hc
    by_cases hw : w i = .I ∨ w i = .Z
    · exact hw
    · exfalso
      have hs : ((StabilizerPairLocalUnitaryInequivalence.sgn (w i) .Z : ℤ) : ℂ) = -1 := by
        cases hwi : w i
        · exact False.elim (hw (Or.inl hwi))
        · norm_num [sgn, anticomm] <;> decide
        · norm_num [sgn, anticomm] <;> decide
        · exact False.elim (hw (Or.inr hwi))
      rw [hs, neg_one_smul, ← h] at hc
      have hz : wordOp w*wordOp (localZ i) = 0 := (by ext x y; have hh := congrFun (congrFun hc x) y; exact neg_eq_self.mp hh.symm)
      exact Units.ne_zero (wordUnit w*wordUnit (localZ i)) hz
  have phase_ne_zero {c : ℂ} (h : Phase c) : c ≠ 0 := (by rcases h with rfl | rfl | rfl | rfl <;> simp)
  have tensor_mul {n : ℕ} (M N : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : tensorOp M * tensorOp N = tensorOp fun i => M i * N i := (by
    classical
    ext x z; simp only [tensorOp, Matrix.mul_apply, Matrix.of_apply]; simp_rw [← Finset.prod_mul_distrib]; rw [Finset.prod_univ_sum, Fintype.piFinset_univ])
  have pauli_sq (p : Pauli) : pauliMatrix p * pauliMatrix p = 1 := (by cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two])
  have word_sq {n : ℕ} (w : (Fin n → Pauli)) : wordOp w * wordOp w = 1 := (by unfold wordOp; rw [tensor_mul]; simp_rw [pauli_sq]; exact tensor_one)
  have localZ_mem {n : ℕ} (i : Fin n) : wordUnit (localZ i) ∈ standardSubgroup n := (by refine ⟨fun j => if j = i then 1 else 0, ?_⟩; congr 1; funext j; by_cases h : j = i <;> simp [zWord, zLetter, localZ, h])
  apply le_antisymm _ hle; intro u hu
  obtain ⟨c,hc,w,hw⟩ := hp hu
  have hz : ∀ i, w i = .I ∨ w i = .Z := (by intro i; apply localZ_forces_z; have hh := congrArg Units.val (hab u hu (wordUnit (localZ i)) (hle (localZ_mem i))); simp only [Units.val_mul, wordUnit, hw, Matrix.smul_mul, Matrix.mul_smul] at hh; exact smul_right_injective (Operator n) (phase_ne_zero hc) hh)
  let b : (Fin n → Fin 2) := fun i => if w i = .I then 0 else 1
  have hb : zWord b = w := (by funext i; obtain h | h := hz i <;> simp [zWord, b, zLetter, h])
  have hreal : c = 1 ∨ c = -1 := by
    rcases hc with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    all_goals
      exfalso
      have he : u*u = (-1 : (Operator n)ˣ) := (by apply Units.ext; simp [hw, h, smul_mul_smul, word_sq, Algebra.algebraMap_eq_smul_one, smul_smul, Complex.I_mul_I])
      exact hn (he ▸ T.mul_mem hu hu)
  obtain h | h := hreal
  · refine ⟨b, ?_⟩
    apply Units.ext; simp [wordUnit, hw, h, hb]
  · exfalso
    have hs : wordUnit w ∈ T := hle ⟨b, by rw [hb]⟩
    have he : u*wordUnit w = (-1 : (Operator n)ˣ) := (by apply Units.ext; simp [hw, h, wordUnit, word_sq, Algebra.algebraMap_eq_smul_one])
    exact hn (he ▸ T.mul_mem hu hs)
private def standardStabilizer (n : ℕ) : StabilizerGroup n := by
  have tensor_mul {n : ℕ} (M N : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : tensorOp M * tensorOp N = tensorOp fun i => M i * N i := (by
    classical
    ext x z; simp only [tensorOp, Matrix.mul_apply, Matrix.of_apply]; simp_rw [← Finset.prod_mul_distrib]; rw [Finset.prod_univ_sum, Fintype.piFinset_univ])
  have pauli_sq (p : Pauli) : pauliMatrix p * pauliMatrix p = 1 := (by cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two])
  have z_letter_mul (a b : Fin 2) : pauliMatrix (zLetter a)*pauliMatrix (zLetter b) = pauliMatrix (zLetter (a+b)) := (by fin_cases a <;> fin_cases b <;> simp [zLetter, pauliMatrix]; exact pauli_sq .Z)
  have z_word_mul {n : ℕ} (a b : (Fin n → Fin 2)) : wordUnit (zWord a)*wordUnit (zWord b) = wordUnit (zWord (a+b)) := by
    apply Units.ext; change tensorOp (fun i => pauliMatrix (zLetter (a i))) *
      tensorOp (fun i => pauliMatrix (zLetter (b i))) =
      tensorOp (fun i => pauliMatrix (zLetter (a i+b i)))
    rw [tensor_mul]; exact congrArg tensorOp (funext fun i => z_letter_mul (a i) (b i))
  have z_word_origin {n : ℕ} (b : (Fin n → Fin 2)) : wordOp (zWord b) 0 0 = 1 := (by simp only [wordOp, tensorOp, Matrix.of_apply]; have hl : ∀ c : Fin 2, pauliMatrix (zLetter c) 0 0 = 1 := (by intro c; fin_cases c <;> simp [zLetter, pauliMatrix, D5.S3.Quantum.FiniteDimensional.qubitZ]); simp [zWord, hl])
  have standard_pauli (n : ℕ) : standardSubgroup n ≤ pauliGroup n := (by rintro u ⟨a,rfl⟩; exact ⟨1,Or.inl rfl,zWord a, by simp [wordUnit]⟩)
  have standard_abelian (n : ℕ) : ∀ u ∈ standardSubgroup n, ∀ v ∈ standardSubgroup n, u*v = v*u := (by rintro u ⟨a,rfl⟩ v ⟨b,rfl⟩; rw [z_word_mul, z_word_mul, add_comm])
  have standard_excludes_neg (n : ℕ) : (-1 : (Operator n)ˣ) ∉ standardSubgroup n := (by rintro ⟨a,ha⟩; have ht := congrArg (fun u : (Operator n)ˣ => (u : Operator n) 0 0) ha; norm_num [ Algebra.algebraMap_eq_smul_one, wordUnit, z_word_origin] at ht)
  exact ⟨standardSubgroup n,standard_pauli n,standard_abelian n,standard_excludes_neg n,standard_maximal n⟩
private def conjugatedStabilizer {n : ℕ} (S : StabilizerGroup n) (U : (Operator n)ˣ) (hU : ∀ u ∈ pauliGroup n, (MulAut.conj U) u ∈ pauliGroup n) : StabilizerGroup n := by
  letI (k : ℕ) : Finite (pauliGroup k) := by
    classical
    have hf (c : ℂ) := Set.finite_range (fun w : Fin k → Pauli => c • wordOp w)
    apply (Set.finite_range_iff (show Function.Injective (fun u : pauliGroup k => (u.val : Operator k)) from fun _ _ h => Subtype.ext (Units.ext h))).mp
    exact (((hf 1).union (hf (-1))).union ((hf Complex.I).union (hf (-Complex.I)))).subset (by rintro _ ⟨u,rfl⟩; dsimp only; obtain ⟨c,hc,w,hw⟩ := u.property; rcases hc with rfl | rfl | rfl | rfl <;> rw [hw] <;> simp only [Set.mem_union, Set.mem_range] <;> aesop)
  have neg_identity_comm {n : ℕ} (u : (Operator n)ˣ) : (-1 : (Operator n)ˣ) * u = u * (-1 : (Operator n)ˣ) := (by apply Units.ext; simp [ Algebra.algebraMap_eq_smul_one])
  have conjugation_fixes_neg {n : ℕ} (U : (Operator n)ˣ) : (MulAut.conj U) ((-1 : (Operator n)ˣ)) = (-1 : (Operator n)ˣ) := (by rw [MulAut.conj_apply,← neg_identity_comm,mul_assoc,mul_inv_cancel,mul_one])
  have normalizes_inverse {n : ℕ} (U : (Operator n)ˣ) (hU : ∀ u ∈ pauliGroup n, (MulAut.conj U) u ∈ pauliGroup n) : ∀ u ∈ pauliGroup n, (MulAut.conj U).symm u ∈ pauliGroup n := (by let f : pauliGroup n → pauliGroup n := fun u => ⟨(MulAut.conj U) u.val,hU u.val u.property⟩; have hi : Function.Injective f := (by intro u v h; apply Subtype.ext; apply (MulAut.conj U).injective; exact congrArg (fun z : pauliGroup n => z.val) h); have hs := Finite.surjective_of_injective hi; intro u hu; obtain ⟨v,hv⟩ := hs ⟨u,hu⟩; have he : (MulAut.conj U) v.val = u := congrArg (fun z : pauliGroup n => z.val) hv; rw [← he, MulEquiv.symm_apply_apply]; exact v.property)
  exact {
    subgroup := S.subgroup.map (MulAut.conj U).toMonoidHom
    pauli := by rintro u ⟨v,hv,rfl⟩; exact hU v (S.pauli hv)
    abelian := by rintro u ⟨v,hv,rfl⟩ w ⟨z,hz,rfl⟩; rw [← map_mul,← map_mul,S.abelian v hv z hz]
    excludes_neg_identity := by rintro ⟨v,hv,he⟩; have hn : v = (-1 : (Operator n)ˣ) := (MulAut.conj U).injective (he.trans (conjugation_fixes_neg U).symm); exact S.excludes_neg_identity (hn ▸ hv)
    maximal := by intro T hp hab hn hle; let K := T.comap (MulAut.conj U).toMonoidHom; have hKp : K ≤ pauliGroup n := (by intro u hu; have hh := normalizes_inverse U hU _ (hp hu); change (MulAut.conj U).symm ((MulAut.conj U) u) ∈ pauliGroup n at hh; rw [MulEquiv.symm_apply_apply] at hh; exact hh); have hKab : ∀ u ∈ K, ∀ v ∈ K, u*v = v*u := (by intro u hu v hv; apply (MulAut.conj U).injective; rw [map_mul,map_mul]; exact hab _ hu _ hv); have hKn : (-1 : (Operator n)ˣ) ∉ K := (by intro hh; apply hn; change (MulAut.conj U) ((-1 : (Operator n)ˣ)) ∈ T at hh; rw [conjugation_fixes_neg] at hh; exact hh); have hSK : S.subgroup ≤ K := (by intro u hu; exact hle ⟨u,hu,rfl⟩); have hKS := S.maximal K hKp hKab hKn hSK; apply le_antisymm _ hle; intro u hu; refine Subgroup.mem_map.mpr ⟨(MulAut.conj U).symm u, ?_, (MulAut.conj U).apply_symm_apply u⟩; rw [← hKS]; change (MulAut.conj U) ((MulAut.conj U).symm u) ∈ T; rw [MulEquiv.apply_symm_apply]; exact hu
  }
private def standardEigen {n : ℕ} (a b : (Fin n → Fin 2)) : ℂ := ∏ i, ((StabilizerPairLocalUnitaryInequivalence.phaseZ (zLetter (a i)) (b i) : ℤ) : ℂ)
open scoped BigOperators
open D5.S3.Quantum.Reduction ComplexConjugate
private def witnessIntegral (x : (Fin 3 → Fin 2)) : GaussianInt := if x 0 = 0 then if x 1 = 0 then (if x 2 = 0 then ⟨1,-1⟩ else ⟨1,1⟩) else -2 else if x 1 = 0 then 2 else if x 2 = 0 then ⟨2,2⟩ else ⟨2,-2⟩
private def witnessVector : EuclideanSpace ℂ ((Fin 3 → Fin 2)) := WithLp.toLp 2 (fun x => (witnessIntegral x : ℂ)/6)
private def rawExpectation (w : (Fin 3 → Pauli)) : GaussianInt := ∑ a, ∑ b, star (witnessIntegral a)*wordZ w a b*witnessIntegral b
private def witness : UnitState 3 := by have witness_integral_norm : (∑ x : (Fin 3 → Fin 2), (witnessIntegral x).norm) = 36 := (by decide +kernel); have witness_norm : ‖witnessVector‖ = 1 := (by have hn : ∑ x : (Fin 3 → Fin 2), Complex.normSq (witnessIntegral x : ℂ) = 36 := (by have hc := congrArg (fun z : ℤ => (z : ℝ)) witness_integral_norm; simpa only [Int.cast_sum, GaussianInt.intCast_real_norm, Int.cast_ofNat] using hc); have hs : ‖witnessVector‖^2 = 1 := (by rw [EuclideanSpace.norm_sq_eq]; simp only [witnessVector, PiLp.toLp_apply, Complex.sq_norm, Complex.normSq_div]; norm_num [Complex.normSq_ofNat]; rw [← Finset.sum_div, hn]; norm_num); nlinarith [norm_nonneg witnessVector]); exact ⟨witnessVector, witness_norm⟩
private def wordCode (w : (Fin 3 → Pauli)) : Fin 64 := ⟨16*pauliDigit (w 0) + 4*pauliDigit (w 1) + pauliDigit (w 2), by have h (p : Pauli) : pauliDigit p < 4 := (by cases p <;> decide); have h0 := h (w 0); have h1 := h (w 1); have h2 := h (w 2); omega⟩
private def expectedTable : Fin 64 → GaussianInt := ![36,16,-12,0, 8,8,-24,0, 0,0,0,8, -12,0,20,0, -8,-8,24,0, -16,0,0,0, 0,0,0,16, 24,24,-8,0, 0,0,0,-8, 0,0,0,16, -16,-32,0,0, 0,0,0,24, -12,0,20,0, -24,-24,8,0, 0,0,0,-24, 4,-16,-12,0]
private def pairing : (Fin 6 → Fin 2) ≃ (Fin 3 → (Fin 2 × Fin 2)) where
  toFun x := ![(x 0,x 3),(x 1,x 4),(x 2,x 5)]
  invFun x := ![(x 0).1,(x 1).1,(x 2).1,(x 0).2,(x 1).2,(x 2).2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv x := by funext i; fin_cases i <;> rfl
private def tensorPair (M : Fin 3 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : Operator 6 := Matrix.of fun x y => ∏ i, M i (pairing x i) (pairing y i)
private def bellRaw : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := Matrix.of fun x b => if x.2.val = (x.1.val+b.1.val)%2 then (if (b.2.val*x.1.val)%2 = 0 then 1 else -1) else 0
private def bellOutput : Pauli → Pauli → Pauli × Pauli | .I,.I => (.I,.I) | .I,.X => (.Z,.I) | .I,.Y => (.Y,.X) | .I,.Z => (.X,.X) | .X,.I => (.I,.X) | .X,.X => (.Z,.X) | .X,.Y => (.Y,.I) | .X,.Z => (.X,.I) | .Y,.I => (.Z,.Y) | .Y,.X => (.I,.Y) | .Y,.Y => (.X,.Z) | .Y,.Z => (.Y,.Z) | .Z,.I => (.Z,.Z) | .Z,.X => (.I,.Z) | .Z,.Y => (.X,.Y) | .Z,.Z => (.Y,.Y)
private def bellPhase : Pauli → Pauli → ℂ | .I,.Y => -1 | .X,.Y => -1 | .Z,.Y => -1 | .Z,.Z => -1 | _,_ => 1
private def bellBlocks (i : Fin 3) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := if i = 2 then 1 else bellRaw
private def blockScale (i : Fin 3) : ℂ := if i = 2 then 1 else 2
private def explicitU : Operator 6 := (1/2 : ℂ) • tensorPair bellBlocks
private def explicitUnit : (Operator 6)ˣ := by
  have tensor_pair_mul (M N : Fin 3 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : tensorPair M*tensorPair N = tensorPair (fun i => M i*N i) := (by
    classical
    ext x z; simp only [tensorPair, Matrix.mul_apply, Matrix.of_apply]; rw [← pairing.symm.sum_comp]; simp only [Equiv.apply_symm_apply]; simp_rw [← Finset.prod_mul_distrib]; rw [Finset.prod_univ_sum, Fintype.piFinset_univ])
  have tensor_pair_one : tensorPair (fun _ => (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) = 1 := by
    classical
    ext x y; simp only [tensorPair, Matrix.of_apply, Matrix.one_apply]
    by_cases h : x = y
    · subst h; simp
    · rw [if_neg h]
      have hn : pairing x ≠ pairing y := fun he => h (pairing.injective he)
      obtain ⟨i,hi⟩ : ∃ i, pairing x i ≠ pairing y i := by by_contra hc; exact hn (funext fun i => not_not.1 fun hi => hc ⟨i,hi⟩)
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  have tensor_pair_smul (c : Fin 3 → ℂ) (M : Fin 3 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : tensorPair (fun i => c i • M i) = (∏ i, c i) • tensorPair M := (by ext x y; simp [tensorPair, Finset.prod_mul_distrib])
  have tensor_pair_star (M : Fin 3 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : (tensorPair M).conjTranspose = tensorPair (fun i => (M i).conjTranspose) := (by ext x y; simp [tensorPair, Matrix.conjTranspose_apply, star_prod])
  have bell_raw_mul_star : bellRaw*bellRaw.conjTranspose = (2 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply])
  have bell_raw_star_mul : bellRaw.conjTranspose*bellRaw = (2 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply])
  have block_scale_prod : (∏ i : Fin 3, blockScale i) = 4 := (by norm_num [blockScale, Fin.prod_univ_succ, Fin.ext_iff])
  have block_mul_star (i : Fin 3) : bellBlocks i*(bellBlocks i).conjTranspose = blockScale i • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
    by_cases hi : i = 2
    · simp [bellBlocks,blockScale,hi]
    · simp [bellBlocks,blockScale,hi,bell_raw_mul_star]
  have block_star_mul (i : Fin 3) : (bellBlocks i).conjTranspose*bellBlocks i = blockScale i • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
    by_cases hi : i = 2
    · simp [bellBlocks,blockScale,hi]
    · simp [bellBlocks,blockScale,hi,bell_raw_star_mul]
  have explicit_u_mul_star : explicitU*explicitU.conjTranspose = 1 := (by simp only [explicitU, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, tensor_pair_star, tensor_pair_mul]; have he : (fun i => bellBlocks i*(bellBlocks i).conjTranspose) = (fun i => blockScale i • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) := funext block_mul_star; rw [he,tensor_pair_smul,block_scale_prod,tensor_pair_one]; norm_num [smul_smul])
  have explicit_u_star_mul : explicitU.conjTranspose*explicitU = 1 := (by simp only [explicitU, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, tensor_pair_star, tensor_pair_mul]; have he : (fun i => (bellBlocks i).conjTranspose*bellBlocks i) = (fun i => blockScale i • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) := funext block_star_mul; rw [he,tensor_pair_smul,block_scale_prod,tensor_pair_one]; norm_num [smul_smul])
  exact ⟨explicitU,explicitU.conjTranspose,explicit_u_mul_star,explicit_u_star_mul⟩
private def outputPair (w : (Fin 6 → Pauli)) (i : Fin 3) : Pauli × Pauli := if i = 2 then (w (Fin.castAdd 3 i),w (Fin.natAdd 3 i)) else bellOutput (w (Fin.castAdd 3 i)) (w (Fin.natAdd 3 i))
private def outputPhase (w : (Fin 6 → Pauli)) (i : Fin 3) : ℂ := if i = 2 then 1 else bellPhase (w (Fin.castAdd 3 i)) (w (Fin.natAdd 3 i))
private def outputWord (w : (Fin 6 → Pauli)) : (Fin 6 → Pauli) := ![(outputPair w 0).1,(outputPair w 1).1,(outputPair w 2).1, (outputPair w 0).2,(outputPair w 1).2,(outputPair w 2).2]
private def explicitGroup : StabilizerGroup 6 := by
  have phase_mul {c d : ℂ} (hc : Phase c) (hd : Phase d) : Phase (c*d) := (by rcases hc with rfl | rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl | rfl <;> simp [Phase, Complex.I_mul_I])
  have phase_prod {n : ℕ} (c : Fin n → ℂ) (h : ∀ i, Phase (c i)) : Phase (∏ i, c i) := (by exact Finset.prod_induction _ _ (fun _ _ => phase_mul) (by simp [Phase]) (fun i _ => h i))
  have pairing_apply (x : (Fin 6 → Fin 2)) (i : Fin 3) : pairing x i = (x (Fin.castAdd 3 i),x (Fin.natAdd 3 i)) := (by fin_cases i <;> rfl)
  have tensor_pair_mul (M N : Fin 3 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : tensorPair M*tensorPair N = tensorPair (fun i => M i*N i) := (by
    classical
    ext x z; simp only [tensorPair, Matrix.mul_apply, Matrix.of_apply]; rw [← pairing.symm.sum_comp]; simp only [Equiv.apply_symm_apply]; simp_rw [← Finset.prod_mul_distrib]; rw [Finset.prod_univ_sum, Fintype.piFinset_univ])
  have tensor_pair_smul (c : Fin 3 → ℂ) (M : Fin 3 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : tensorPair (fun i => c i • M i) = (∏ i, c i) • tensorPair M := (by ext x y; simp [tensorPair, Finset.prod_mul_distrib])
  have tensor_pair_star (M : Fin 3 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : (tensorPair M).conjTranspose = tensorPair (fun i => (M i).conjTranspose) := (by ext x y; simp [tensorPair, Matrix.conjTranspose_apply, star_prod])
  have word_pair (w : (Fin 6 → Pauli)) : wordOp w = tensorPair (fun i => Matrix.kronecker (pauliMatrix (w (Fin.castAdd 3 i))) (pauliMatrix (w (Fin.natAdd 3 i)))) := by
    ext x y; simp only [wordOp, tensorOp, tensorPair, Matrix.kronecker, Matrix.kroneckerMap, Matrix.of_apply, pairing_apply]
    let f : Fin (3+3) → ℂ := fun i => pauliMatrix (w i) (x i) (y i)
    change (∏ i, f i) = ∏ i : Fin 3, f (Fin.castAdd 3 i)*f (Fin.natAdd 3 i)
    calc
      (∏ i, f i) = (∏ i : Fin 3, f (Fin.castAdd 3 i)) * ∏ i : Fin 3, f (Fin.natAdd 3 i) := Fin.prod_univ_add f
      _ = _ := Finset.prod_mul_distrib.symm
  have bell_phase_mem (p q : Pauli) : Phase (bellPhase p q) := (by cases p <;> cases q <;> simp [bellPhase, Phase])
  have bell_normalizes_II : bellRaw*Matrix.kronecker (pauliMatrix .I) (pauliMatrix .I)*bellRaw.conjTranspose = (2*bellPhase .I .I) • Matrix.kronecker (pauliMatrix (bellOutput .I .I).1) (pauliMatrix (bellOutput .I .I).2) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.kronecker, Matrix.kroneckerMap, bellOutput, bellPhase, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, pauliMatrix, qubitX, qubitZ] <;> ring)
  have bell_normalizes_IX : bellRaw*Matrix.kronecker (pauliMatrix .I) (pauliMatrix .X)*bellRaw.conjTranspose = (2*bellPhase .I .X) • Matrix.kronecker (pauliMatrix (bellOutput .I .X).1) (pauliMatrix (bellOutput .I .X).2) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.kronecker, Matrix.kroneckerMap, bellOutput, bellPhase, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, pauliMatrix, qubitX, qubitZ] <;> ring)
  have bell_normalizes_IY : bellRaw*Matrix.kronecker (pauliMatrix .I) (pauliMatrix .Y)*bellRaw.conjTranspose = (2*bellPhase .I .Y) • Matrix.kronecker (pauliMatrix (bellOutput .I .Y).1) (pauliMatrix (bellOutput .I .Y).2) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.kronecker, Matrix.kroneckerMap, bellOutput, bellPhase, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, pauliMatrix, qubitX, qubitZ] <;> ring)
  have bell_normalizes_IZ : bellRaw*Matrix.kronecker (pauliMatrix .I) (pauliMatrix .Z)*bellRaw.conjTranspose = (2*bellPhase .I .Z) • Matrix.kronecker (pauliMatrix (bellOutput .I .Z).1) (pauliMatrix (bellOutput .I .Z).2) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.kronecker, Matrix.kroneckerMap, bellOutput, bellPhase, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, pauliMatrix, qubitX, qubitZ] <;> ring)
  have bell_normalizes_XI : bellRaw*Matrix.kronecker (pauliMatrix .X) (pauliMatrix .I)*bellRaw.conjTranspose = (2*bellPhase .X .I) • Matrix.kronecker (pauliMatrix (bellOutput .X .I).1) (pauliMatrix (bellOutput .X .I).2) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.kronecker, Matrix.kroneckerMap, bellOutput, bellPhase, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, pauliMatrix, qubitX, qubitZ] <;> ring)
  have bell_normalizes_XX : bellRaw*Matrix.kronecker (pauliMatrix .X) (pauliMatrix .X)*bellRaw.conjTranspose = (2*bellPhase .X .X) • Matrix.kronecker (pauliMatrix (bellOutput .X .X).1) (pauliMatrix (bellOutput .X .X).2) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.kronecker, Matrix.kroneckerMap, bellOutput, bellPhase, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, pauliMatrix, qubitX, qubitZ] <;> ring)
  have bell_normalizes_XY : bellRaw*Matrix.kronecker (pauliMatrix .X) (pauliMatrix .Y)*bellRaw.conjTranspose = (2*bellPhase .X .Y) • Matrix.kronecker (pauliMatrix (bellOutput .X .Y).1) (pauliMatrix (bellOutput .X .Y).2) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.kronecker, Matrix.kroneckerMap, bellOutput, bellPhase, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, pauliMatrix, qubitX, qubitZ] <;> ring)
  have bell_normalizes_XZ : bellRaw*Matrix.kronecker (pauliMatrix .X) (pauliMatrix .Z)*bellRaw.conjTranspose = (2*bellPhase .X .Z) • Matrix.kronecker (pauliMatrix (bellOutput .X .Z).1) (pauliMatrix (bellOutput .X .Z).2) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.kronecker, Matrix.kroneckerMap, bellOutput, bellPhase, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, pauliMatrix, qubitX, qubitZ] <;> ring)
  have bell_normalizes_YI : bellRaw*Matrix.kronecker (pauliMatrix .Y) (pauliMatrix .I)*bellRaw.conjTranspose = (2*bellPhase .Y .I) • Matrix.kronecker (pauliMatrix (bellOutput .Y .I).1) (pauliMatrix (bellOutput .Y .I).2) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.kronecker, Matrix.kroneckerMap, bellOutput, bellPhase, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, pauliMatrix, qubitX, qubitZ] <;> ring)
  have bell_normalizes_YX : bellRaw*Matrix.kronecker (pauliMatrix .Y) (pauliMatrix .X)*bellRaw.conjTranspose = (2*bellPhase .Y .X) • Matrix.kronecker (pauliMatrix (bellOutput .Y .X).1) (pauliMatrix (bellOutput .Y .X).2) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.kronecker, Matrix.kroneckerMap, bellOutput, bellPhase, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, pauliMatrix, qubitX, qubitZ] <;> ring)
  have bell_normalizes_YY : bellRaw*Matrix.kronecker (pauliMatrix .Y) (pauliMatrix .Y)*bellRaw.conjTranspose = (2*bellPhase .Y .Y) • Matrix.kronecker (pauliMatrix (bellOutput .Y .Y).1) (pauliMatrix (bellOutput .Y .Y).2) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.kronecker, Matrix.kroneckerMap, bellOutput, bellPhase, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, pauliMatrix, qubitX, qubitZ] <;> ring)
  have bell_normalizes_YZ : bellRaw*Matrix.kronecker (pauliMatrix .Y) (pauliMatrix .Z)*bellRaw.conjTranspose = (2*bellPhase .Y .Z) • Matrix.kronecker (pauliMatrix (bellOutput .Y .Z).1) (pauliMatrix (bellOutput .Y .Z).2) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.kronecker, Matrix.kroneckerMap, bellOutput, bellPhase, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, pauliMatrix, qubitX, qubitZ] <;> ring)
  have bell_normalizes_ZI : bellRaw*Matrix.kronecker (pauliMatrix .Z) (pauliMatrix .I)*bellRaw.conjTranspose = (2*bellPhase .Z .I) • Matrix.kronecker (pauliMatrix (bellOutput .Z .I).1) (pauliMatrix (bellOutput .Z .I).2) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.kronecker, Matrix.kroneckerMap, bellOutput, bellPhase, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, pauliMatrix, qubitX, qubitZ] <;> ring)
  have bell_normalizes_ZX : bellRaw*Matrix.kronecker (pauliMatrix .Z) (pauliMatrix .X)*bellRaw.conjTranspose = (2*bellPhase .Z .X) • Matrix.kronecker (pauliMatrix (bellOutput .Z .X).1) (pauliMatrix (bellOutput .Z .X).2) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.kronecker, Matrix.kroneckerMap, bellOutput, bellPhase, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, pauliMatrix, qubitX, qubitZ] <;> ring)
  have bell_normalizes_ZY : bellRaw*Matrix.kronecker (pauliMatrix .Z) (pauliMatrix .Y)*bellRaw.conjTranspose = (2*bellPhase .Z .Y) • Matrix.kronecker (pauliMatrix (bellOutput .Z .Y).1) (pauliMatrix (bellOutput .Z .Y).2) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.kronecker, Matrix.kroneckerMap, bellOutput, bellPhase, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, pauliMatrix, qubitX, qubitZ] <;> ring)
  have bell_normalizes_ZZ : bellRaw*Matrix.kronecker (pauliMatrix .Z) (pauliMatrix .Z)*bellRaw.conjTranspose = (2*bellPhase .Z .Z) • Matrix.kronecker (pauliMatrix (bellOutput .Z .Z).1) (pauliMatrix (bellOutput .Z .Z).2) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.kronecker, Matrix.kroneckerMap, bellOutput, bellPhase, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, pauliMatrix, qubitX, qubitZ] <;> ring)
  have bell_normalizes (p q : Pauli) : bellRaw*Matrix.kronecker (pauliMatrix p) (pauliMatrix q)*bellRaw.conjTranspose = (2*bellPhase p q) • Matrix.kronecker (pauliMatrix (bellOutput p q).1) (pauliMatrix (bellOutput p q).2) := by
    cases p <;> cases q
    · exact bell_normalizes_II
    · exact bell_normalizes_IX
    · exact bell_normalizes_IY
    · exact bell_normalizes_IZ
    · exact bell_normalizes_XI
    · exact bell_normalizes_XX
    · exact bell_normalizes_XY
    · exact bell_normalizes_XZ
    · exact bell_normalizes_YI
    · exact bell_normalizes_YX
    · exact bell_normalizes_YY
    · exact bell_normalizes_YZ
    · exact bell_normalizes_ZI
    · exact bell_normalizes_ZX
    · exact bell_normalizes_ZY
    · exact bell_normalizes_ZZ
  have block_scale_prod : (∏ i : Fin 3, blockScale i) = 4 := (by norm_num [blockScale, Fin.prod_univ_succ, Fin.ext_iff])
  have block_normalizes (w : (Fin 6 → Pauli)) (i : Fin 3) : bellBlocks i*Matrix.kronecker (pauliMatrix (w (Fin.castAdd 3 i))) (pauliMatrix (w (Fin.natAdd 3 i)))*(bellBlocks i).conjTranspose = (blockScale i*outputPhase w i) • Matrix.kronecker (pauliMatrix (outputPair w i).1) (pauliMatrix (outputPair w i).2) := by
    by_cases hi : i = 2
    · simp [bellBlocks,blockScale,outputPhase,outputPair,hi]
    · simpa [bellBlocks,blockScale,outputPhase,outputPair,hi] using
        bell_normalizes (w (Fin.castAdd 3 i)) (w (Fin.natAdd 3 i))
  have explicit_normalizes_word (w : (Fin 6 → Pauli)) : explicitU*wordOp w*explicitU.conjTranspose = (∏ i, outputPhase w i) • wordOp (outputWord w) := (by simp only [explicitU, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, tensor_pair_star]; rw [word_pair,tensor_pair_mul,tensor_pair_mul]; have he : (fun i => bellBlocks i*Matrix.kronecker (pauliMatrix (w (Fin.castAdd 3 i))) (pauliMatrix (w (Fin.natAdd 3 i)))* (bellBlocks i).conjTranspose) = (fun i => (blockScale i*outputPhase w i) • Matrix.kronecker (pauliMatrix (outputPair w i).1) (pauliMatrix (outputPair w i).2)) := funext (block_normalizes w); rw [he,tensor_pair_smul,Finset.prod_mul_distrib,block_scale_prod]; have ho : tensorPair (fun i => Matrix.kronecker (pauliMatrix (outputPair w i).1) (pauliMatrix (outputPair w i).2)) = wordOp (outputWord w) := (by rw [word_pair]; apply congrArg tensorPair; funext i; fin_cases i <;> rfl); rw [ho]; norm_num [smul_smul]; congr 1; ring)
  have explicit_normalizes (u : (Operator 6)ˣ) (hu : u ∈ pauliGroup 6) : explicitUnit*u*explicitUnit⁻¹ ∈ pauliGroup 6 := by
    obtain ⟨c,hc,w,hw⟩ := hu
    refine ⟨c*(∏ i, outputPhase w i), phase_mul hc (phase_prod _ ?_), outputWord w, ?_⟩
    · intro i
      unfold outputPhase
      split_ifs
      · exact Or.inl rfl
      · exact bell_phase_mem _ _
    · change explicitU*(u : Operator 6)*explicitU.conjTranspose = _
      rw [hw,Matrix.mul_smul,Matrix.smul_mul,explicit_normalizes_word,smul_smul]
  exact conjugatedStabilizer (standardStabilizer 6) explicitUnit explicit_normalizes
private def explicitVector (b : (Fin 6 → Fin 2)) : State 6 := fun x => explicitU x b
private def explicitBasis : StabilizerBasis 3 3 := by
  have tensor_one {n : ℕ} : tensorOp (fun _ : Fin n => (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
    classical
    ext x y; simp only [tensorOp, Matrix.of_apply, Matrix.one_apply, Fintype.prod_boole, ← funext_iff]
  have explicit_spans : Submodule.span ℂ (Set.range explicitVector) = ⊤ := by
    have tensor_pair_mul (M N : Fin 3 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : tensorPair M*tensorPair N = tensorPair (fun i => M i*N i) := (by
      classical
      ext x z; simp only [tensorPair, Matrix.mul_apply, Matrix.of_apply]; rw [← pairing.symm.sum_comp]; simp only [Equiv.apply_symm_apply]; simp_rw [← Finset.prod_mul_distrib]; rw [Finset.prod_univ_sum, Fintype.piFinset_univ])
    have tensor_pair_one : tensorPair (fun _ => (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) = 1 := by
      classical
      ext x y; simp only [tensorPair, Matrix.of_apply, Matrix.one_apply]
      by_cases h : x = y
      · subst h; simp
      · rw [if_neg h]
        have hn : pairing x ≠ pairing y := fun he => h (pairing.injective he)
        obtain ⟨i,hi⟩ : ∃ i, pairing x i ≠ pairing y i := by by_contra hc; exact hn (funext fun i => not_not.1 fun hi => hc ⟨i,hi⟩)
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    have tensor_pair_smul (c : Fin 3 → ℂ) (M : Fin 3 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : tensorPair (fun i => c i • M i) = (∏ i, c i) • tensorPair M := (by ext x y; simp [tensorPair, Finset.prod_mul_distrib])
    have tensor_pair_star (M : Fin 3 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : (tensorPair M).conjTranspose = tensorPair (fun i => (M i).conjTranspose) := (by ext x y; simp [tensorPair, Matrix.conjTranspose_apply, star_prod])
    have bell_raw_mul_star : bellRaw*bellRaw.conjTranspose = (2 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply])
    have block_scale_prod : (∏ i : Fin 3, blockScale i) = 4 := (by norm_num [blockScale, Fin.prod_univ_succ, Fin.ext_iff])
    have block_mul_star (i : Fin 3) : bellBlocks i*(bellBlocks i).conjTranspose = blockScale i • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
      by_cases hi : i = 2
      · simp [bellBlocks,blockScale,hi]
      · simp [bellBlocks,blockScale,hi,bell_raw_mul_star]
    have explicit_u_mul_star : explicitU*explicitU.conjTranspose = 1 := (by simp only [explicitU, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, tensor_pair_star, tensor_pair_mul]; have he : (fun i => bellBlocks i*(bellBlocks i).conjTranspose) = (fun i => blockScale i • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) := funext block_mul_star; rw [he,tensor_pair_smul,block_scale_prod,tensor_pair_one]; norm_num [smul_smul])
    classical
    apply eq_top_iff.mpr; intro v _
    have hv : v = ∑ b, (Matrix.mulVec explicitU.conjTranspose v b) • explicitVector b := by
      calc
        v = Matrix.mulVec explicitU (Matrix.mulVec explicitU.conjTranspose v) := by rw [Matrix.mulVec_mulVec,explicit_u_mul_star,Matrix.one_mulVec]
        _ = _ := by ext x; simp [Matrix.mulVec,dotProduct,explicitVector,Finset.sum_apply,mul_comm]
    rw [hv]; apply Submodule.sum_mem; intro b _; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b,rfl⟩)
  have z_letter_diagonal (b x y : Fin 2) : pauliMatrix (zLetter b) x y = ((StabilizerPairLocalUnitaryInequivalence.phaseZ (zLetter b) x : ℤ) : ℂ) * (if x = y then 1 else 0) := (by fin_cases b <;> fin_cases x <;> fin_cases y <;> simp [zLetter,phaseZ,pauliMatrix, D5.S3.Quantum.FiniteDimensional.qubitZ])
  have z_word_diagonal {n : ℕ} (a : (Fin n → Fin 2)) : wordOp (zWord a) = Matrix.diagonal (standardEigen a) := (by
    classical
    ext x y; simp only [wordOp,tensorOp,zWord,Matrix.of_apply,z_letter_diagonal]; rw [Finset.prod_mul_distrib]; have hd : (∏ i, (if x i = y i then 1 else 0 : ℂ)) = (1 : Operator n) x y := (by exact congrFun (congrFun (@tensor_one n) x) y); rw [hd]; simp [standardEigen,Matrix.diagonal_apply,Matrix.one_apply])
  have standard_eigen_single {n : ℕ} (a b : (Fin n → Fin 2)) : Matrix.mulVec (wordOp (zWord a)) (Pi.single b 1) = standardEigen a b • Pi.single b 1 := by
    rw [z_word_diagonal,Matrix.mulVec_single_one]; ext x
    by_cases hx : x = b
    · subst hx; simp [Matrix.col,Matrix.diagonal_apply]
    · simp [Matrix.col,Matrix.diagonal_apply,hx,Pi.single_eq_of_ne hx]
  have tensor_pair_mul (M N : Fin 3 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : tensorPair M*tensorPair N = tensorPair (fun i => M i*N i) := (by
    classical
    ext x z; simp only [tensorPair, Matrix.mul_apply, Matrix.of_apply]; rw [← pairing.symm.sum_comp]; simp only [Equiv.apply_symm_apply]; simp_rw [← Finset.prod_mul_distrib]; rw [Finset.prod_univ_sum, Fintype.piFinset_univ])
  have tensor_pair_one : tensorPair (fun _ => (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) = 1 := by
    classical
    ext x y; simp only [tensorPair, Matrix.of_apply, Matrix.one_apply]
    by_cases h : x = y
    · subst h; simp
    · rw [if_neg h]
      have hn : pairing x ≠ pairing y := fun he => h (pairing.injective he)
      obtain ⟨i,hi⟩ : ∃ i, pairing x i ≠ pairing y i := by by_contra hc; exact hn (funext fun i => not_not.1 fun hi => hc ⟨i,hi⟩)
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  have tensor_pair_smul (c : Fin 3 → ℂ) (M : Fin 3 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : tensorPair (fun i => c i • M i) = (∏ i, c i) • tensorPair M := (by ext x y; simp [tensorPair, Finset.prod_mul_distrib])
  have tensor_pair_star (M : Fin 3 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : (tensorPair M).conjTranspose = tensorPair (fun i => (M i).conjTranspose) := (by ext x y; simp [tensorPair, Matrix.conjTranspose_apply, star_prod])
  have bell_raw_star_mul : bellRaw.conjTranspose*bellRaw = (2 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply])
  have block_scale_prod : (∏ i : Fin 3, blockScale i) = 4 := (by norm_num [blockScale, Fin.prod_univ_succ, Fin.ext_iff])
  have block_star_mul (i : Fin 3) : (bellBlocks i).conjTranspose*bellBlocks i = blockScale i • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
    by_cases hi : i = 2
    · simp [bellBlocks,blockScale,hi]
    · simp [bellBlocks,blockScale,hi,bell_raw_star_mul]
  have explicit_u_star_mul : explicitU.conjTranspose*explicitU = 1 := (by simp only [explicitU, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, tensor_pair_star, tensor_pair_mul]; have he : (fun i => (bellBlocks i).conjTranspose*bellBlocks i) = (fun i => blockScale i • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) := funext block_star_mul; rw [he,tensor_pair_smul,block_scale_prod,tensor_pair_one]; norm_num [smul_smul])
  have explicit_vector_single (b : (Fin 6 → Fin 2)) : explicitVector b = Matrix.mulVec explicitU (Pi.single b 1) := (by rw [Matrix.mulVec_single_one]; rfl)
  have explicit_orthonormal (b c : (Fin 6 → Fin 2)) : (∑ x, star (explicitVector b x)*explicitVector c x) = if b = c then 1 else 0 := (by have hh := congrFun (congrFun explicit_u_star_mul b) c; simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,explicitVector,Matrix.one_apply] using hh)
  have explicit_common_eigen (b : (Fin 6 → Fin 2)) : CommonEigenvector explicitGroup (explicitVector b) := (by rintro u ⟨s,hs,he⟩; obtain ⟨a,rfl⟩ := hs; refine ⟨standardEigen a b, ?_⟩; have hu : (u : Operator 6) = explicitU*wordOp (zWord a)*explicitU.conjTranspose := (by exact congrArg Units.val he.symm); rw [hu,explicit_vector_single,Matrix.mulVec_mulVec]; rw [mul_assoc (explicitU*wordOp (zWord a)) explicitU.conjTranspose explicitU, explicit_u_star_mul,mul_one,← Matrix.mulVec_mulVec,standard_eigen_single,Matrix.mulVec_smul])
  exact ⟨explicitGroup,explicitVector,explicit_orthonormal,explicit_common_eigen,explicit_spans⟩
private def bellInput : Pauli → (Fin 2 × Fin 2) | .I => (0,0) | .X => (0,1) | .Y => (1,1) | .Z => (1,0)
private def correlatedWord (p : (Fin 2 → Pauli)) (d a : Fin 2) : (Fin 6 → Pauli) := ![p 0,p 1,zLetter d,p 0,p 1,zLetter a]
private def inputBits (p : (Fin 2 → Pauli)) (d a : Fin 2) : (Fin 6 → Fin 2) := ![(bellInput (p 0)).1,(bellInput (p 1)).1,d, (bellInput (p 0)).2,(bellInput (p 1)).2,a]
private lemma thirtytwo_in_span (p : (Fin 2 → Pauli)) (d : Fin 2) : wordOp (Fin.snoc p (zLetter d)) ∈ Submodule.span ℂ (Set.range (fun b => mu witness (explicitBasis.vectors b))) := by
  have subgroup_compress_in_effect_span {n m : ℕ} (B : StabilizerBasis n m) (hres : (∑ b, rankOneDensity (B.vectors b)) = (1 : Operator (n+m))) (ψ : UnitState m) (u : (Operator (n+m))ˣ) (hu : u ∈ B.group.subgroup) : IsometricCompression.compress (ancillaEmbedding ψ) (u : Operator (n+m)) ∈ Submodule.span ℂ (Set.range (fun b => mu ψ (B.vectors b))) := by
    classical
    let eigen (b : (Fin (n+m) → Fin 2)) := Classical.choose (B.common_eigen b u hu)
    have he (b : (Fin (n+m) → Fin 2)) : Matrix.mulVec (u : Operator (n+m)) (B.vectors b) = eigen b • B.vectors b := Classical.choose_spec (B.common_eigen b u hu)
    have hm (b : (Fin (n+m) → Fin 2)) : (u : Operator (n+m))*rankOneDensity (B.vectors b) = eigen b • rankOneDensity (B.vectors b) := (by unfold rankOneDensity; rw [Matrix.mul_vecMulVec,he b]; ext x y; simp [Matrix.vecMulVec_apply,mul_assoc])
    have hd : (u : Operator (n+m)) = ∑ b, eigen b • rankOneDensity (B.vectors b) := by
      calc
        (u : Operator (n+m)) = (u : Operator (n+m))*(∑ b, rankOneDensity (B.vectors b)) := by rw [hres,mul_one]
        _ = ∑ b, eigen b • rankOneDensity (B.vectors b) := by rw [Matrix.mul_sum]; exact Finset.sum_congr rfl (fun b _ => hm b)
    change (compressLinear ψ) (u : Operator (n+m)) ∈ _; rw [hd,map_sum]; apply Submodule.sum_mem; intro b _; rw [map_smul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b,rfl⟩)
  have phase_ne_zero {c : ℂ} (h : Phase c) : c ≠ 0 := (by rcases h with rfl | rfl | rfl | rfl <;> simp)
  have phase_mul {c d : ℂ} (hc : Phase c) (hd : Phase d) : Phase (c*d) := (by rcases hc with rfl | rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl | rfl <;> simp [Phase, Complex.I_mul_I])
  have phase_prod {n : ℕ} (c : Fin n → ℂ) (h : ∀ i, Phase (c i)) : Phase (∏ i, c i) := (by exact Finset.prod_induction _ _ (fun _ _ => phase_mul) (by simp [Phase]) (fun i _ => h i))
  have word_split {n m : ℕ} (w : (Fin (n+m) → Pauli)) (d e : (Fin n → Fin 2)) (a b : (Fin m → Fin 2)) : wordOp w (Fin.addCases d a) (Fin.addCases e b) = wordOp (restrictData w) d e * wordOp (restrictAncilla w) a b := (by simp only [wordOp, tensorOp, Matrix.of_apply]; rw [Fin.prod_univ_add]; simp [Fin.addCases, restrictData, restrictAncilla])
  have compress_pauli {n m : ℕ} (w : (Fin (n+m) → Pauli)) (c : ℂ) (ψ : UnitState m) : IsometricCompression.compress (ancillaEmbedding ψ) (c • wordOp w) = (c*expectation (restrictAncilla w) ψ) • wordOp (restrictData w) := by
    have compression_entry (A : Operator (n+m)) (x y : Fin n → Fin 2) : IsometricCompression.compress (ancillaEmbedding ψ) A x y = ∑ a, ∑ b, star (ψ.val a)*A (Fin.addCases x a) (Fin.addCases y b)*ψ.val b := by classical
      simp only [IsometricCompression.compress, Matrix.mul_apply, Matrix.conjTranspose_apply]; simp_rw [← (Fin.appendEquiv (α := Fin 2) n m).sum_comp]; simp only [Fintype.sum_prod_type, ancillaEmbedding, Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Matrix.kronecker, Matrix.one_apply, Matrix.replicateCol_apply, Equiv.symm_apply_apply]; simp [Fin.appendEquiv, Fin.append, Finset.sum_mul, apply_ite, ite_mul, Finset.sum_ite_irrel] <;> rw [Finset.sum_comm]
    ext x y; simp only [compression_entry, Matrix.smul_apply, smul_eq_mul, word_split, expectation]
    calc
      _ = ∑ a, (c*wordOp (restrictData w) x y)*
          ∑ b, star (ψ.val a)*wordOp (restrictAncilla w) a b*ψ.val b := by
        apply Finset.sum_congr rfl; intro a _; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
      _ = (c*wordOp (restrictData w) x y)*
          ∑ a, ∑ b, star (ψ.val a)*wordOp (restrictAncilla w) a b*ψ.val b :=
        (Finset.mul_sum _ _ _).symm
      _ = _ := by ring
  have integral_pauli_cast (p : Pauli) (x y : Fin 2) : (pauliZ p x y : ℂ) = pauliMatrix p x y := (by cases p <;> fin_cases x <;> fin_cases y <;> simp [pauliZ, pauliMatrix, qubitX, qubitZ, GaussianInt.toComplex_def'])
  have integral_word_cast (w : (Fin 3 → Pauli)) (x y : (Fin 3 → Fin 2)) : (wordZ w x y : ℂ) = wordOp w x y := (by simp only [wordZ, wordOp, tensorOp, Matrix.of_apply]; rw [map_prod]; exact Finset.prod_congr rfl (fun i _ => integral_pauli_cast (w i) (x i) (y i)))
  have expectation_raw (w : (Fin 3 → Pauli)) : expectation w witness = (rawExpectation w : ℂ)/36 := by
    simp only [expectation, witness, witnessVector, PiLp.toLp_apply, rawExpectation, map_sum, map_mul, GaussianInt.toComplex_star, integral_word_cast]
    calc
      _ = ∑ a, (∑ b, star (witnessIntegral a : ℂ)*wordOp w a b*(witnessIntegral b : ℂ))/36 := by apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro b _; simp only [star_div₀, star_ofNat]; ring
      _ = _ := (Finset.sum_div _ _ _).symm
  have raw_pairs_nonzero (p : (Fin 2 → Pauli)) : rawExpectation (Fin.snoc p .I) ≠ 0 ∨ rawExpectation (Fin.snoc p .Z) ≠ 0 := (by fin_cases p <;> decide +kernel)
  have witness_pairs_nonzero (p : (Fin 2 → Pauli)) : expectation (Fin.snoc p .I) witness ≠ 0 ∨ expectation (Fin.snoc p .Z) witness ≠ 0 := (by have h := raw_pairs_nonzero p; simpa only [expectation_raw, ne_eq, div_eq_zero_iff, show (36 : ℂ) ≠ 0 by norm_num, or_false, GaussianInt.toComplex_eq_zero] using h)
  have pairing_apply (x : (Fin 6 → Fin 2)) (i : Fin 3) : pairing x i = (x (Fin.castAdd 3 i),x (Fin.natAdd 3 i)) := (by fin_cases i <;> rfl)
  have tensor_pair_mul (M N : Fin 3 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : tensorPair M*tensorPair N = tensorPair (fun i => M i*N i) := (by
    classical
    ext x z; simp only [tensorPair, Matrix.mul_apply, Matrix.of_apply]; rw [← pairing.symm.sum_comp]; simp only [Equiv.apply_symm_apply]; simp_rw [← Finset.prod_mul_distrib]; rw [Finset.prod_univ_sum, Fintype.piFinset_univ])
  have tensor_pair_one : tensorPair (fun _ => (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) = 1 := by
    classical
    ext x y; simp only [tensorPair, Matrix.of_apply, Matrix.one_apply]
    by_cases h : x = y
    · subst h; simp
    · rw [if_neg h]
      have hn : pairing x ≠ pairing y := fun he => h (pairing.injective he)
      obtain ⟨i,hi⟩ : ∃ i, pairing x i ≠ pairing y i := by by_contra hc; exact hn (funext fun i => not_not.1 fun hi => hc ⟨i,hi⟩)
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  have tensor_pair_smul (c : Fin 3 → ℂ) (M : Fin 3 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : tensorPair (fun i => c i • M i) = (∏ i, c i) • tensorPair M := (by ext x y; simp [tensorPair, Finset.prod_mul_distrib])
  have tensor_pair_star (M : Fin 3 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : (tensorPair M).conjTranspose = tensorPair (fun i => (M i).conjTranspose) := (by ext x y; simp [tensorPair, Matrix.conjTranspose_apply, star_prod])
  have word_pair (w : (Fin 6 → Pauli)) : wordOp w = tensorPair (fun i => Matrix.kronecker (pauliMatrix (w (Fin.castAdd 3 i))) (pauliMatrix (w (Fin.natAdd 3 i)))) := by
    ext x y; simp only [wordOp, tensorOp, tensorPair, Matrix.kronecker, Matrix.kroneckerMap, Matrix.of_apply, pairing_apply]
    let f : Fin (3+3) → ℂ := fun i => pauliMatrix (w i) (x i) (y i)
    change (∏ i, f i) = ∏ i : Fin 3, f (Fin.castAdd 3 i)*f (Fin.natAdd 3 i)
    calc
      (∏ i, f i) = (∏ i : Fin 3, f (Fin.castAdd 3 i)) * ∏ i : Fin 3, f (Fin.natAdd 3 i) := Fin.prod_univ_add f
      _ = _ := Finset.prod_mul_distrib.symm
  have bell_raw_mul_star : bellRaw*bellRaw.conjTranspose = (2 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply])
  have bell_phase_mem (p q : Pauli) : Phase (bellPhase p q) := (by cases p <;> cases q <;> simp [bellPhase, Phase])
  have bell_normalizes_II : bellRaw*Matrix.kronecker (pauliMatrix .I) (pauliMatrix .I)*bellRaw.conjTranspose = (2*bellPhase .I .I) • Matrix.kronecker (pauliMatrix (bellOutput .I .I).1) (pauliMatrix (bellOutput .I .I).2) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.kronecker, Matrix.kroneckerMap, bellOutput, bellPhase, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, pauliMatrix, qubitX, qubitZ] <;> ring)
  have bell_normalizes_IX : bellRaw*Matrix.kronecker (pauliMatrix .I) (pauliMatrix .X)*bellRaw.conjTranspose = (2*bellPhase .I .X) • Matrix.kronecker (pauliMatrix (bellOutput .I .X).1) (pauliMatrix (bellOutput .I .X).2) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.kronecker, Matrix.kroneckerMap, bellOutput, bellPhase, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, pauliMatrix, qubitX, qubitZ] <;> ring)
  have bell_normalizes_IY : bellRaw*Matrix.kronecker (pauliMatrix .I) (pauliMatrix .Y)*bellRaw.conjTranspose = (2*bellPhase .I .Y) • Matrix.kronecker (pauliMatrix (bellOutput .I .Y).1) (pauliMatrix (bellOutput .I .Y).2) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.kronecker, Matrix.kroneckerMap, bellOutput, bellPhase, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, pauliMatrix, qubitX, qubitZ] <;> ring)
  have bell_normalizes_IZ : bellRaw*Matrix.kronecker (pauliMatrix .I) (pauliMatrix .Z)*bellRaw.conjTranspose = (2*bellPhase .I .Z) • Matrix.kronecker (pauliMatrix (bellOutput .I .Z).1) (pauliMatrix (bellOutput .I .Z).2) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.kronecker, Matrix.kroneckerMap, bellOutput, bellPhase, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, pauliMatrix, qubitX, qubitZ] <;> ring)
  have bell_normalizes_XI : bellRaw*Matrix.kronecker (pauliMatrix .X) (pauliMatrix .I)*bellRaw.conjTranspose = (2*bellPhase .X .I) • Matrix.kronecker (pauliMatrix (bellOutput .X .I).1) (pauliMatrix (bellOutput .X .I).2) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.kronecker, Matrix.kroneckerMap, bellOutput, bellPhase, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, pauliMatrix, qubitX, qubitZ] <;> ring)
  have bell_normalizes_XX : bellRaw*Matrix.kronecker (pauliMatrix .X) (pauliMatrix .X)*bellRaw.conjTranspose = (2*bellPhase .X .X) • Matrix.kronecker (pauliMatrix (bellOutput .X .X).1) (pauliMatrix (bellOutput .X .X).2) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.kronecker, Matrix.kroneckerMap, bellOutput, bellPhase, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, pauliMatrix, qubitX, qubitZ] <;> ring)
  have bell_normalizes_XY : bellRaw*Matrix.kronecker (pauliMatrix .X) (pauliMatrix .Y)*bellRaw.conjTranspose = (2*bellPhase .X .Y) • Matrix.kronecker (pauliMatrix (bellOutput .X .Y).1) (pauliMatrix (bellOutput .X .Y).2) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.kronecker, Matrix.kroneckerMap, bellOutput, bellPhase, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, pauliMatrix, qubitX, qubitZ] <;> ring)
  have bell_normalizes_XZ : bellRaw*Matrix.kronecker (pauliMatrix .X) (pauliMatrix .Z)*bellRaw.conjTranspose = (2*bellPhase .X .Z) • Matrix.kronecker (pauliMatrix (bellOutput .X .Z).1) (pauliMatrix (bellOutput .X .Z).2) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.kronecker, Matrix.kroneckerMap, bellOutput, bellPhase, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, pauliMatrix, qubitX, qubitZ] <;> ring)
  have bell_normalizes_YI : bellRaw*Matrix.kronecker (pauliMatrix .Y) (pauliMatrix .I)*bellRaw.conjTranspose = (2*bellPhase .Y .I) • Matrix.kronecker (pauliMatrix (bellOutput .Y .I).1) (pauliMatrix (bellOutput .Y .I).2) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.kronecker, Matrix.kroneckerMap, bellOutput, bellPhase, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, pauliMatrix, qubitX, qubitZ] <;> ring)
  have bell_normalizes_YX : bellRaw*Matrix.kronecker (pauliMatrix .Y) (pauliMatrix .X)*bellRaw.conjTranspose = (2*bellPhase .Y .X) • Matrix.kronecker (pauliMatrix (bellOutput .Y .X).1) (pauliMatrix (bellOutput .Y .X).2) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.kronecker, Matrix.kroneckerMap, bellOutput, bellPhase, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, pauliMatrix, qubitX, qubitZ] <;> ring)
  have bell_normalizes_YY : bellRaw*Matrix.kronecker (pauliMatrix .Y) (pauliMatrix .Y)*bellRaw.conjTranspose = (2*bellPhase .Y .Y) • Matrix.kronecker (pauliMatrix (bellOutput .Y .Y).1) (pauliMatrix (bellOutput .Y .Y).2) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.kronecker, Matrix.kroneckerMap, bellOutput, bellPhase, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, pauliMatrix, qubitX, qubitZ] <;> ring)
  have bell_normalizes_YZ : bellRaw*Matrix.kronecker (pauliMatrix .Y) (pauliMatrix .Z)*bellRaw.conjTranspose = (2*bellPhase .Y .Z) • Matrix.kronecker (pauliMatrix (bellOutput .Y .Z).1) (pauliMatrix (bellOutput .Y .Z).2) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.kronecker, Matrix.kroneckerMap, bellOutput, bellPhase, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, pauliMatrix, qubitX, qubitZ] <;> ring)
  have bell_normalizes_ZI : bellRaw*Matrix.kronecker (pauliMatrix .Z) (pauliMatrix .I)*bellRaw.conjTranspose = (2*bellPhase .Z .I) • Matrix.kronecker (pauliMatrix (bellOutput .Z .I).1) (pauliMatrix (bellOutput .Z .I).2) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.kronecker, Matrix.kroneckerMap, bellOutput, bellPhase, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, pauliMatrix, qubitX, qubitZ] <;> ring)
  have bell_normalizes_ZX : bellRaw*Matrix.kronecker (pauliMatrix .Z) (pauliMatrix .X)*bellRaw.conjTranspose = (2*bellPhase .Z .X) • Matrix.kronecker (pauliMatrix (bellOutput .Z .X).1) (pauliMatrix (bellOutput .Z .X).2) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.kronecker, Matrix.kroneckerMap, bellOutput, bellPhase, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, pauliMatrix, qubitX, qubitZ] <;> ring)
  have bell_normalizes_ZY : bellRaw*Matrix.kronecker (pauliMatrix .Z) (pauliMatrix .Y)*bellRaw.conjTranspose = (2*bellPhase .Z .Y) • Matrix.kronecker (pauliMatrix (bellOutput .Z .Y).1) (pauliMatrix (bellOutput .Z .Y).2) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.kronecker, Matrix.kroneckerMap, bellOutput, bellPhase, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, pauliMatrix, qubitX, qubitZ] <;> ring)
  have bell_normalizes_ZZ : bellRaw*Matrix.kronecker (pauliMatrix .Z) (pauliMatrix .Z)*bellRaw.conjTranspose = (2*bellPhase .Z .Z) • Matrix.kronecker (pauliMatrix (bellOutput .Z .Z).1) (pauliMatrix (bellOutput .Z .Z).2) := (by ext x y; rcases x with ⟨x0,x1⟩; rcases y with ⟨y0,y1⟩; fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;> norm_num [bellRaw, Matrix.kronecker, Matrix.kroneckerMap, bellOutput, bellPhase, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply, pauliMatrix, qubitX, qubitZ] <;> ring)
  have bell_normalizes (p q : Pauli) : bellRaw*Matrix.kronecker (pauliMatrix p) (pauliMatrix q)*bellRaw.conjTranspose = (2*bellPhase p q) • Matrix.kronecker (pauliMatrix (bellOutput p q).1) (pauliMatrix (bellOutput p q).2) := by
    cases p <;> cases q
    · exact bell_normalizes_II
    · exact bell_normalizes_IX
    · exact bell_normalizes_IY
    · exact bell_normalizes_IZ
    · exact bell_normalizes_XI
    · exact bell_normalizes_XX
    · exact bell_normalizes_XY
    · exact bell_normalizes_XZ
    · exact bell_normalizes_YI
    · exact bell_normalizes_YX
    · exact bell_normalizes_YY
    · exact bell_normalizes_YZ
    · exact bell_normalizes_ZI
    · exact bell_normalizes_ZX
    · exact bell_normalizes_ZY
    · exact bell_normalizes_ZZ
  have block_scale_prod : (∏ i : Fin 3, blockScale i) = 4 := (by norm_num [blockScale, Fin.prod_univ_succ, Fin.ext_iff])
  have block_mul_star (i : Fin 3) : bellBlocks i*(bellBlocks i).conjTranspose = blockScale i • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
    by_cases hi : i = 2
    · simp [bellBlocks,blockScale,hi]
    · simp [bellBlocks,blockScale,hi,bell_raw_mul_star]
  have explicit_u_mul_star : explicitU*explicitU.conjTranspose = 1 := (by simp only [explicitU, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, tensor_pair_star, tensor_pair_mul]; have he : (fun i => bellBlocks i*(bellBlocks i).conjTranspose) = (fun i => blockScale i • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) := funext block_mul_star; rw [he,tensor_pair_smul,block_scale_prod,tensor_pair_one]; norm_num [smul_smul])
  have block_normalizes (w : (Fin 6 → Pauli)) (i : Fin 3) : bellBlocks i*Matrix.kronecker (pauliMatrix (w (Fin.castAdd 3 i))) (pauliMatrix (w (Fin.natAdd 3 i)))*(bellBlocks i).conjTranspose = (blockScale i*outputPhase w i) • Matrix.kronecker (pauliMatrix (outputPair w i).1) (pauliMatrix (outputPair w i).2) := by
    by_cases hi : i = 2
    · simp [bellBlocks,blockScale,outputPhase,outputPair,hi]
    · simpa [bellBlocks,blockScale,outputPhase,outputPair,hi] using
        bell_normalizes (w (Fin.castAdd 3 i)) (w (Fin.natAdd 3 i))
  have explicit_normalizes_word (w : (Fin 6 → Pauli)) : explicitU*wordOp w*explicitU.conjTranspose = (∏ i, outputPhase w i) • wordOp (outputWord w) := (by simp only [explicitU, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, tensor_pair_star]; rw [word_pair,tensor_pair_mul,tensor_pair_mul]; have he : (fun i => bellBlocks i*Matrix.kronecker (pauliMatrix (w (Fin.castAdd 3 i))) (pauliMatrix (w (Fin.natAdd 3 i)))* (bellBlocks i).conjTranspose) = (fun i => (blockScale i*outputPhase w i) • Matrix.kronecker (pauliMatrix (outputPair w i).1) (pauliMatrix (outputPair w i).2)) := funext (block_normalizes w); rw [he,tensor_pair_smul,Finset.prod_mul_distrib,block_scale_prod]; have ho : tensorPair (fun i => Matrix.kronecker (pauliMatrix (outputPair w i).1) (pauliMatrix (outputPair w i).2)) = wordOp (outputWord w) := (by rw [word_pair]; apply congrArg tensorPair; funext i; fin_cases i <;> rfl); rw [ho]; norm_num [smul_smul]; congr 1; ring)
  have explicit_resolution : (∑ b, rankOneDensity (explicitVector b)) = (1 : Operator 6) := by
    calc
      (∑ b, rankOneDensity (explicitVector b)) = explicitU*explicitU.conjTranspose := by ext x y; simp [rankOneDensity,explicitVector,Matrix.mul_apply,Matrix.conjTranspose_apply, Finset.sum_apply,Matrix.sum_apply,Matrix.vecMulVec_apply]
      _ = 1 := explicit_u_mul_star
  have bell_input_output (p : Pauli) : bellOutput (zLetter (bellInput p).1) (zLetter (bellInput p).2) = (p,p) := (by cases p <;> simp [bellInput,zLetter,bellOutput])
  have correlated_output (p : (Fin 2 → Pauli)) (d a : Fin 2) : outputWord (zWord (inputBits p d a)) = correlatedWord p d a := (by funext j; fin_cases j <;> simp [outputWord,correlatedWord,outputPair,zWord,inputBits, bell_input_output,Fin.ext_iff])
  have correlated_mem (p : (Fin 2 → Pauli)) (d a : Fin 2) : ∃ u ∈ explicitGroup.subgroup, ∃ c : ℂ, c ≠ 0 ∧ (u : Operator 6) = c • wordOp (correlatedWord p d a) := by
    let w := zWord (inputBits p d a)
    let u := (MulAut.conj explicitUnit) (wordUnit w)
    have hu : u ∈ explicitGroup.subgroup := ⟨wordUnit w, ⟨inputBits p d a,rfl⟩, rfl⟩
    refine ⟨u,hu, ∏ i, outputPhase w i, ?_, ?_⟩
    · apply phase_ne_zero
      apply phase_prod; intro i; unfold outputPhase
      split_ifs
      · exact Or.inl rfl
      · exact bell_phase_mem _ _
    · change explicitU*wordOp w*explicitU.conjTranspose = _
      rw [explicit_normalizes_word,correlated_output]
  have correlated_restrict_data (p : (Fin 2 → Pauli)) (d a : Fin 2) : restrictData (n := 3) (m := 3) (correlatedWord p d a) = Fin.snoc p (zLetter d) := (by funext i; fin_cases i <;> rfl)
  have correlated_restrict_ancilla (p : (Fin 2 → Pauli)) (d a : Fin 2) : restrictAncilla (n := 3) (m := 3) (correlatedWord p d a) = Fin.snoc p (zLetter a) := (by funext i; fin_cases i <;> rfl)
  let V := Submodule.span ℂ (Set.range (fun b => mu witness (explicitBasis.vectors b)))
  obtain h | h := witness_pairs_nonzero p
  · obtain ⟨u,hu,c,hc,he⟩ := correlated_mem p d 0
    have hs := subgroup_compress_in_effect_span explicitBasis explicit_resolution witness u hu
    rw [he,compress_pauli,correlated_restrict_data,correlated_restrict_ancilla] at hs
    have hz : c*expectation (Fin.snoc p (zLetter 0)) witness ≠ 0 := (by exact mul_ne_zero hc (by simpa [zLetter] using h))
    have hh := V.smul_mem (c*expectation (Fin.snoc p (zLetter 0)) witness)⁻¹ hs
    simpa only [smul_smul,inv_mul_cancel₀ hz,one_smul] using hh
  · obtain ⟨u,hu,c,hc,he⟩ := correlated_mem p d 1
    have hs := subgroup_compress_in_effect_span explicitBasis explicit_resolution witness u hu
    rw [he,compress_pauli,correlated_restrict_data,correlated_restrict_ancilla] at hs
    have hz : c*expectation (Fin.snoc p (zLetter 1)) witness ≠ 0 := (by exact mul_ne_zero hc (by simpa [zLetter] using h))
    have hh := V.smul_mem (c*expectation (Fin.snoc p (zLetter 1)) witness)⁻¹ hs
    simpa only [smul_smul,inv_mul_cancel₀ hz,one_smul] using hh
private lemma explicit_lower_bound : 32 ≤ smu witness explicitBasis := by
  have word_trace_pair {n : ℕ} (v w : (Fin n → Pauli)) : Matrix.trace (wordOp v * wordOp w) = if v = w then (2 : ℂ)^n else 0 := by
    have tensor_mul {n : ℕ} (M N : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : tensorOp M * tensorOp N = tensorOp fun i => M i * N i := (by
      classical
      ext x z; simp only [tensorOp, Matrix.mul_apply, Matrix.of_apply]; simp_rw [← Finset.prod_mul_distrib]; rw [Finset.prod_univ_sum, Fintype.piFinset_univ])
    have tensor_trace {n : ℕ} (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : Matrix.trace (tensorOp M) = ∏ i, Matrix.trace (M i) := (by
      classical
      simp only [Matrix.trace, Matrix.diag, tensorOp, Matrix.of_apply]; rw [Finset.prod_univ_sum, Fintype.piFinset_univ])
    have pauli_trace_pair (p q : Pauli) : Matrix.trace (pauliMatrix p * pauliMatrix q) = if p = q then 2 else 0 := (by cases p <;> cases q <;> simp [pauliMatrix, qubitX, qubitZ, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num)
    classical
    unfold wordOp; rw [tensor_mul, tensor_trace]; simp_rw [pauli_trace_pair]
    simp only [Fintype.prod_ite_zero, ← funext_iff, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have word_linearIndependent (n : ℕ) : LinearIndependent ℂ (@wordOp n) := by
    classical
    apply linearIndependent_iff'.2; intro s c h v hv; have ht := congrArg (fun A : Operator n => Matrix.trace (wordOp v * A)) h; simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, word_trace_pair, mul_ite, mul_zero, Matrix.mul_zero, Matrix.trace_zero] at ht; rw [Finset.sum_ite_eq s v] at ht; simp only [hv, if_true] at ht; exact (mul_eq_zero.mp ht).resolve_right (pow_ne_zero _ (by norm_num))
  have append_z_injective : Function.Injective (fun x : (Fin 2 → Pauli) × Fin 2 => (Fin.snoc x.1 (zLetter x.2) : Fin 3 → Pauli)) := (by intro x y h; have hp : x.1 = y.1 := (by funext i; have hh := congrFun h (Fin.castSucc i); simpa only [Fin.snoc_castSucc] using hh); have hz : zLetter x.2 = zLetter y.2 := (by simpa only [Fin.snoc_last] using congrFun h (Fin.last 2)); have hd : x.2 = y.2 := (by rcases x with ⟨p,d⟩; rcases y with ⟨q,a⟩; fin_cases d <;> fin_cases a <;> simp_all [zLetter]); exact Prod.ext hp hd); let f : (Fin 2 → Pauli) × Fin 2 → Operator 3 := fun x => wordOp (Fin.snoc x.1 (zLetter x.2)); have hli : LinearIndependent ℂ f := (word_linearIndependent 3).comp _ append_z_injective; have hcard : Fintype.card ((Fin 2 → Pauli) × Fin 2) = 32 := (by decide); have hdim : Module.finrank ℂ (Submodule.span ℂ (Set.range f)) = 32 := (by rw [finrank_span_eq_card hli,hcard]); have hspan : Submodule.span ℂ (Set.range f) ≤ Submodule.span ℂ (Set.range (fun b => mu witness (explicitBasis.vectors b))) := (by apply Submodule.span_le.mpr; rintro A ⟨⟨p,d⟩,rfl⟩; exact thirtytwo_in_span p d); rw [← hdim]; exact Submodule.finrank_mono hspan
theorem result : ¬ claim := by
  have integral_pauli_cast (p : Pauli) (x y : Fin 2) : (pauliZ p x y : ℂ) = pauliMatrix p x y := (by cases p <;> fin_cases x <;> fin_cases y <;> simp [pauliZ, pauliMatrix, qubitX, qubitZ, GaussianInt.toComplex_def'])
  have integral_word_cast (w : (Fin 3 → Pauli)) (x y : (Fin 3 → Fin 2)) : (wordZ w x y : ℂ) = wordOp w x y := (by simp only [wordZ, wordOp, tensorOp, Matrix.of_apply]; rw [map_prod]; exact Finset.prod_congr rfl (fun i _ => integral_pauli_cast (w i) (x i) (y i)))
  have expectation_raw (w : (Fin 3 → Pauli)) : expectation w witness = (rawExpectation w : ℂ)/36 := by
    simp only [expectation, witness, witnessVector, PiLp.toLp_apply, rawExpectation, map_sum, map_mul, GaussianInt.toComplex_star, integral_word_cast]
    calc
      _ = ∑ a, (∑ b, star (witnessIntegral a : ℂ)*wordOp w a b*(witnessIntegral b : ℂ))/36 := by apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro b _; simp only [star_div₀, star_ofNat]; ring
      _ = _ := (Finset.sum_div _ _ _).symm
  have expectation_table (w : (Fin 3 → Pauli)) : rawExpectation w = expectedTable (wordCode w) := (by fin_cases w <;> decide +kernel)
  have expected_support_card : (Finset.univ.filter (fun w : (Fin 3 → Pauli) => expectedTable (wordCode w) ≠ 0)).card = 31 := (by decide +kernel)
  have witness_support_card : Nat.card {w : (Fin 3 → Pauli) // expectation w witness ≠ 0} = 31 := (by have hp : ∀ w : (Fin 3 → Pauli), expectation w witness ≠ 0 ↔ expectedTable (wordCode w) ≠ 0 := (by intro w; rw [expectation_raw, ne_eq, div_eq_zero_iff]; simp only [show (36 : ℂ) ≠ 0 by norm_num, or_false, GaussianInt.toComplex_eq_zero, expectation_table]); have he : {w : (Fin 3 → Pauli) // expectation w witness ≠ 0} ≃ {w : (Fin 3 → Pauli) // expectedTable (wordCode w) ≠ 0} := Equiv.subtypeEquivRight hp; rw [Nat.card_congr he, Nat.card_eq_fintype_card, Fintype.card_subtype]; exact expected_support_card)
  have witness_upper_bound (B : StabilizerBasis 3 3) (hm : MaximallyEntangled B) : smu witness B ≤ 31 := (by have h := maximal_entangled_support_bound witness B hm; rw [witness_support_card] at h; exact h)
  intro h
  obtain ⟨B,hm,hopt⟩ := h 3 3 witness
  have hu := witness_upper_bound B hm
  have hl := explicit_lower_bound
  have ho := hopt explicitBasis
  omega
#print axioms result
end
end D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
