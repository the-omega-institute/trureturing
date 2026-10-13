/- GID: D5/S3/Quantum/Recovery/PhaseBoundaryReferenceReduction
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PhaseBoundaryReferenceReduction
   mirror-E: none(waiver:research-interface)
   anchors: []
   utility: none
   digest: Receiver output-label symmetrization for the actual coherent recovery task. -/

import D5.S3.Quantum.Recovery.PhaseBoundarySourceModel

noncomputable section

namespace D5.S3.Quantum.Recovery.PhaseBoundaryReferenceReduction

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Recovery.PhaseBoundaryFlagInstrument
open D5.S3.Quantum.Recovery.PhaseBoundarySourceModel
open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

private theorem receiver_entry {M A B : Type}
    [Fintype M] [DecidableEq M] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (D : QuantumChannel A B)
    (X : CStarMatrix (M × A) (M × A) ℂ) (p q : M × B) :
    (receiverChannel D).toCompletelyPositiveMap X p q =
      D.toCompletelyPositiveMap
        (CStarMatrix.ofMatrix fun a b => X (p.1, a) (q.1, b)) p.2 q.2 := by
  exact PhaseBoundarySourceModel.receiver_reference (F := Unit) D
    (CStarMatrix.ofMatrix fun a b => X a.2 b.2) () () p.1 q.1 p.2 q.2

private theorem reference_comp {F A B C : Type}
    [Fintype F] [DecidableEq F] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (G : QuantumChannel A B) (H : QuantumChannel B C)
    (X : CStarMatrix (F × A) (F × A) ℂ) :
    referenceAction (H.comp G) X = referenceAction H (referenceAction G X) := rfl

private theorem receiver_reference {F M A B : Type}
    [Fintype F] [DecidableEq F] [Fintype M] [DecidableEq M]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (D : QuantumChannel A B)
    (X : CStarMatrix (F × (M × A)) (F × (M × A)) ℂ)
    (f g : F) (m n : M) (b c : B) :
    referenceAction (receiverChannel D) X (f, (m, b)) (g, (n, c)) =
      D.toCompletelyPositiveMap
        (CStarMatrix.ofMatrix fun a d => X (f, (m, a)) (g, (n, d))) b c :=
  receiver_entry D _ _ _

private theorem phase_exists {A : Type} [Fintype A] [DecidableEq A]
    (c : A → ℝ) (hc : ∀ a, c a ^ 2 = 1) :
    ∃ Z : QuantumChannel A A, ∀ X : CStarMatrix A A ℂ, ∀ a b,
      Z.toCompletelyPositiveMap X a b = (c a : ℂ) * X a b * (c b : ℂ) := by
  let K : Matrix A A ℂ := Matrix.diagonal fun a => (c a : ℂ)
  have hK : (∑ _ : Unit, K.conjTranspose * K) = 1 := by
    simp only [Fintype.sum_unique]
    ext a b
    by_cases hab : a = b
    · subst b
      have hh : (c a : ℂ) ^ 2 = 1 := by exact_mod_cast hc a
      simpa [K, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal,
        ← pow_two] using hh
    · simp [K, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal, hab, Ne.symm hab]
  obtain ⟨Z, hZ⟩ := finite_kraus_quantum_channel (fun _ : Unit => K) hK
  refine ⟨Z, fun X a b => ?_⟩
  have hh := congrFun (congrFun (hZ (CStarMatrix.ofMatrix.symm X)) a) b
  simpa [K, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal,
    mul_assoc, apply_ite] using hh

private def phaseChannel {A : Type} [Fintype A] [DecidableEq A]
    (c : A → ℝ) (hc : ∀ a, c a ^ 2 = 1) : QuantumChannel A A :=
  (phase_exists c hc).choose

private theorem phase_entry {A : Type} [Fintype A] [DecidableEq A]
    (c : A → ℝ) (hc : ∀ a, c a ^ 2 = 1)
    (X : CStarMatrix A A ℂ) (a b : A) :
    (phaseChannel c hc).toCompletelyPositiveMap X a b =
      (c a : ℂ) * X a b * (c b : ℂ) :=
  (phase_exists c hc).choose_spec X a b

private theorem sign_square (s : Qubit) : flagSign s ^ 2 = 1 := by
  fin_cases s <;> norm_num [flagSign]

private def inputPhase : QuantumChannel Qubit Qubit := phaseChannel flagSign sign_square

abbrev Output := Qubit × (Qubit × Qubit)

private def outputPhase : QuantumChannel Output Output :=
  phaseChannel (fun p => flagSign p.2.1) (fun p => sign_square p.2.1)

private theorem input_phase_entry (X : CStarMatrix Qubit Qubit ℂ) (a b : Qubit) :
    inputPhase.toCompletelyPositiveMap X a b =
      (flagSign a : ℂ) * X a b * (flagSign b : ℂ) := phase_entry _ _ _ _ _

private theorem output_phase_entry (X : CStarMatrix Output Output ℂ) (a b : Output) :
    outputPhase.toCompletelyPositiveMap X a b =
      (flagSign a.2.1 : ℂ) * X a b * (flagSign b.2.1 : ℂ) := phase_entry _ _ _ _ _

section Source

variable (ell beta gamma : ℝ) (w : Qubit → ℝ)
    (hl : 0 ≤ ell) (hu : ell ≤ 1) (hb : 0 < beta)
    (hw : ∀ j, 0 ≤ w j) (hmax : ∀ j, w j ≤ beta / (beta ^ 2 + gamma ^ 2))

private abbrev N := sourceChannel ell beta gamma w hl hu hb hw hmax
private abbrev V := targetChannel ell hl hu

private theorem source_entry {F : Type} [Fintype F] [DecidableEq F]
    (X : CStarMatrix (F × Qubit) (F × Qubit) ℂ) (f g : F) (p q : Output) :
    referenceAction (N ell beta gamma w hl hu hb hw hmax) X (f, p) (g, q) =
      ∑ j, X (f, j) (g, j) * omega ell beta gamma (w j) p q :=
  PhaseBoundarySourceModel.source_reference ell beta gamma w hl hu hb hw hmax X f g p q

private theorem target_entry {F : Type} [Fintype F] [DecidableEq F]
    (X : CStarMatrix (F × Qubit) (F × Qubit) ℂ) (f g : F) (p q : Output) :
    referenceAction (V ell hl hu) X (f, p) (g, q) =
      X (f, p.2.1) (g, q.2.1) * xi ell (p.1, p.2.2) * star (xi ell (q.1, q.2.2)) :=
  PhaseBoundarySourceModel.target_reference ell hl hu X f g p q

private abbrev decoded (D : QuantumChannel (Qubit × Qubit) (Qubit × Qubit)) :=
  (receiverChannel (M := Qubit) D).comp (N ell beta gamma w hl hu hb hw hmax)

private theorem decoded_pinch {F : Type} [Fintype F] [DecidableEq F]
    (D : QuantumChannel (Qubit × Qubit) (Qubit × Qubit))
    (X : CStarMatrix (F × Qubit) (F × Qubit) ℂ)
    (f g : F) (p q : Output) :
    referenceAction (decoded ell beta gamma w hl hu hb hw hmax
      (FlagInstrument.extract D).decoder) X (f, p) (g, q) =
      if p.2.1 = q.2.1 then
        referenceAction (decoded ell beta gamma w hl hu hb hw hmax D) X (f, p) (g, q)
      else 0 := by
  let Z := referenceAction (N ell beta gamma w hl hu hb hw hmax) X
  let Y : CStarMatrix ((F × Qubit) × (Qubit × Qubit))
      ((F × Qubit) × (Qubit × Qubit)) ℂ :=
    CStarMatrix.ofMatrix fun a b => Z (a.1.1, (a.1.2, a.2)) (b.1.1, (b.1.2, b.2))
  have hY : FlagDiagonal Y := by
    intro a b hab
    change Z (a.1.1, (a.1.2, a.2)) (b.1.1, (b.1.2, b.2)) = 0
    dsimp only [Z]
    rw [source_entry]
    simp [omega, hab]
  have hh := common_flag_instrument_complete.{0, 0, 0, 0, 0, 0}.2 D (F × Qubit) Y hY
  have he := congrArg (fun T => T ((f, p.1), p.2) ((g, q.1), q.2)) hh
  rcases p with ⟨m, j, a⟩
  rcases q with ⟨n, k, b⟩
  simp only [decoded, reference_comp, receiver_reference]
  exact he

private def twistInput {F : Type} [Fintype F] [DecidableEq F]
    (rho : DensityState (F × Qubit)) : DensityState (F × Qubit) :=
  (receiverChannel (M := F) inputPhase).mapState rho

private theorem twist_input_entry {F : Type} [Fintype F] [DecidableEq F]
    (rho : DensityState (F × Qubit)) (f g : F) (a b : Qubit) :
    (twistInput rho).1 (f, a) (g, b) =
      (flagSign a : ℂ) * rho.1 (f, a) (g, b) * (flagSign b : ℂ) := by
  change (receiverChannel inputPhase).toCompletelyPositiveMap rho.1 (f, a) (g, b) = _
  rw [receiver_entry, input_phase_entry]
  rfl

private theorem source_twist {F : Type} [Fintype F] [DecidableEq F]
    (rho : DensityState (F × Qubit)) :
    referenceAction (N ell beta gamma w hl hu hb hw hmax) (twistInput rho).1 =
      referenceAction (N ell beta gamma w hl hu hb hw hmax) rho.1 := by
  ext ⟨f, p⟩ ⟨g, q⟩
  rw [source_entry, source_entry]
  simp only [twist_input_entry]
  apply Finset.sum_congr rfl
  intro j _
  have hs : (flagSign j : ℂ) ^ 2 = 1 := by exact_mod_cast sign_square j
  linear_combination rho.1 (f, j) (g, j) * omega ell beta gamma (w j) p q * hs

private theorem target_twist {F : Type} [Fintype F] [DecidableEq F]
    (rho : DensityState (F × Qubit)) :
    (receiverChannel (M := F) outputPhase).toCompletelyPositiveMap
      (referenceAction (V ell hl hu) (twistInput rho).1) =
      referenceAction (V ell hl hu) rho.1 := by
  ext ⟨f, p⟩ ⟨g, q⟩
  rw [receiver_entry, output_phase_entry]
  change (flagSign p.2.1 : ℂ) *
    referenceAction (V ell hl hu) (twistInput rho).1 (f, p) (g, q) *
      (flagSign q.2.1 : ℂ) = _
  simp_rw [target_entry ell hl hu, twist_input_entry]
  have hp : (flagSign p.2.1 : ℂ) ^ 2 = 1 := by exact_mod_cast sign_square p.2.1
  have hq : (flagSign q.2.1 : ℂ) ^ 2 = 1 := by exact_mod_cast sign_square q.2.1
  calc
    _ = ((flagSign p.2.1 : ℂ) ^ 2) * ((flagSign q.2.1 : ℂ) ^ 2) *
      (rho.1 (f, p.2.1) (g, q.2.1) * xi ell (p.1, p.2.2) *
        star (xi ell (q.1, q.2.2))) := by ring
    _ = _ := by rw [hp, hq]; ring

private theorem decoded_twist {F : Type} [Fintype F] [DecidableEq F]
    (D : QuantumChannel (Qubit × Qubit) (Qubit × Qubit))
    (rho : DensityState (F × Qubit)) :
    referenceAction (decoded ell beta gamma w hl hu hb hw hmax D) (twistInput rho).1 =
      referenceAction (decoded ell beta gamma w hl hu hb hw hmax D) rho.1 := by
  simp only [decoded, reference_comp]
  rw [source_twist]

private theorem symmetrized_state {F : Type} [Fintype F] [DecidableEq F]
    (D : QuantumChannel (Qubit × Qubit) (Qubit × Qubit))
    (rho : DensityState (F × Qubit)) :
    referenceAction (decoded ell beta gamma w hl hu hb hw hmax
      (FlagInstrument.extract D).decoder) rho.1 =
      (1 / 2 : ℂ) •
        (referenceAction (decoded ell beta gamma w hl hu hb hw hmax D) rho.1 +
          (receiverChannel (M := F) outputPhase).toCompletelyPositiveMap
            (referenceAction (decoded ell beta gamma w hl hu hb hw hmax D) rho.1)) := by
  ext ⟨f, m, j, a⟩ ⟨g, n, k, b⟩
  rw [decoded_pinch]
  change (if j = k then _ else 0) = (1 / 2 : ℂ) * (_ + _)
  rw [receiver_entry, output_phase_entry]
  fin_cases j <;> fin_cases k <;> simp [flagSign] <;> ring

end Source

private theorem distance_bounded {A B : Type}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (G H : QuantumChannel A B) :
    BddAbove ({0} ∪ {x : ℝ | ∃ n : ℕ, ∃ rho : DensityState (Fin n × A),
      x = referenceError G H rho}) := by
  refine ⟨2, ?_⟩
  rintro x (hx | ⟨n, rho, rfl⟩)
  · have hx0 : x = 0 := hx
    subst x
    norm_num
  · have hh := traceDistance_le_one (referenceState G rho) (referenceState H rho)
    change referenceError G H rho / 2 ≤ 1 at hh
    linarith

private theorem error_le_distance {A B : Type}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (G H : QuantumChannel A B) (n : ℕ) (rho : DensityState (Fin n × A)) :
    referenceError G H rho ≤ diamondDistance G H :=
  le_csSup (distance_bounded G H) (Or.inr ⟨n, rho, rfl⟩)

private theorem distance_nonnegative {A B : Type}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (G H : QuantumChannel A B) : 0 ≤ diamondDistance G H :=
  le_csSup (distance_bounded G H) (Or.inl (Set.mem_singleton 0))

/-- Output-label pinching is lossless for the complete-reference minimax error.
The coherent target is kept intact: the comparison uses a phase orbit of the
input, rather than assuming that the target is label diagonal. -/
theorem output_label_symmetrization
    (ell beta gamma : ℝ) (w : Qubit → ℝ)
    (hl : 0 ≤ ell) (hu : ell ≤ 1) (hb : 0 < beta)
    (hw : ∀ j, 0 ≤ w j) (hmax : ∀ j, w j ≤ beta / (beta ^ 2 + gamma ^ 2))
    (D : QuantumChannel (Qubit × Qubit) (Qubit × Qubit)) :
    diamondDistance (decoded ell beta gamma w hl hu hb hw hmax
        (FlagInstrument.extract D).decoder) (targetChannel ell hl hu) ≤
      diamondDistance (decoded ell beta gamma w hl hu hb hw hmax D)
        (targetChannel ell hl hu) := by
  let G := decoded ell beta gamma w hl hu hb hw hmax D
  let S := decoded ell beta gamma w hl hu hb hw hmax (FlagInstrument.extract D).decoder
  let T := targetChannel ell hl hu
  let E := diamondDistance G T
  change sSup _ ≤ E
  apply csSup_le
  · exact ⟨0, Or.inl (Set.mem_singleton 0)⟩
  rintro x (hx | ⟨n, rho, rfl⟩)
  · have hh : x = 0 := hx
    subst x
    exact distance_nonnegative G T
  let rho' := twistInput rho
  let Z := receiverChannel (M := Fin n) outputPhase
  let a := referenceState G rho
  let b := referenceState T rho
  let a' := referenceState G rho'
  let b' := referenceState T rho'
  have hA : a'.1 = a.1 := decoded_twist ell beta gamma w hl hu hb hw hmax D rho
  have hB : Z.toCompletelyPositiveMap b'.1 = b.1 :=
    target_twist ell hl hu rho
  let U : Matrix (Fin n × Output) (Fin n × Output) ℂ :=
    CStarMatrix.ofMatrix.symm a.1 - CStarMatrix.ofMatrix.symm b.1
  let W : Matrix (Fin n × Output) (Fin n × Output) ℂ :=
    CStarMatrix.ofMatrix.symm (Z.mapState a').1 - CStarMatrix.ofMatrix.symm (Z.mapState b').1
  have hdiff :
      CStarMatrix.ofMatrix.symm (referenceState S rho).1 - CStarMatrix.ofMatrix.symm b.1 =
        (1 / 2 : ℂ) • (U + W) := by
    have hs := symmetrized_state ell beta gamma w hl hu hb hw hmax D rho
    change referenceAction S rho.1 = (1 / 2 : ℂ) • (a.1 + Z.toCompletelyPositiveMap a.1) at hs
    ext p q
    have he := congrArg (fun X => X p q) hs
    change (referenceState S rho).1 p q - b.1 p q =
      (1 / 2 : ℂ) * (a.1 p q - b.1 p q +
        ((Z.mapState a').1 p q - (Z.mapState b').1 p q))
    change referenceAction S rho.1 p q - b.1 p q = _
    change referenceAction S rho.1 p q =
      (1 / 2 : ℂ) * (a.1 p q + Z.toCompletelyPositiveMap a.1 p q) at he
    change referenceAction S rho.1 p q - b.1 p q =
      (1 / 2 : ℂ) * (a.1 p q - b.1 p q +
        (Z.toCompletelyPositiveMap a'.1 p q - Z.toCompletelyPositiveMap b'.1 p q))
    rw [hA, hB, he]
    ring
  have hU : traceNorm U ≤ E := error_le_distance G T n rho
  have hW : traceNorm W ≤ E := by
    have hc := traceDistance_contract Z a' b'
    change traceNorm W / 2 ≤ referenceError G T rho' / 2 at hc
    have hh := error_le_distance G T n rho'
    linarith
  change traceNorm (CStarMatrix.ofMatrix.symm (referenceState S rho).1 -
    CStarMatrix.ofMatrix.symm b.1) ≤ E
  rw [hdiff]
  obtain ⟨Q, hQ⟩ := (traceNorm_eq_max_re_tr_U ((1 / 2 : ℂ) • (U + W))).1
  have hQU := (traceNorm_eq_max_re_tr_U U).2 ⟨Q, rfl⟩
  have hQW := (traceNorm_eq_max_re_tr_U W).2 ⟨Q, rfl⟩
  have hsplit : (((Q.val * ((1 / 2 : ℂ) • (U + W))).trace).re) =
      (1 / 2 : ℝ) * ((Q.val * U).trace).re +
        (1 / 2 : ℝ) * ((Q.val * W).trace).re := by
    simp [Matrix.mul_add, Matrix.trace_add, Matrix.trace_smul]
  rw [← hQ, hsplit]
  linarith

end D5.S3.Quantum.Recovery.PhaseBoundaryReferenceReduction
