import D5.S3.Quantum.Recovery.MatrixUnitDecoder
import Reg.Support.DependentFamily

open scoped Matrix BigOperators
open _root_.D5.S3.Quantum.Recovery.MatrixUnitDecoder
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder

noncomputable section
universe u v

namespace Gram

abbrev signature : Signature where
  Params := (d : Type u) × Type v
  State := fun p => p.1 → p.1 → Matrix p.2 p.2 ℂ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output := fun _ p => p.1 → p.1 → Matrix p.2 p.2 ℂ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro x; exact nomatch x⟩

def actual : Realization signature.{u, v} :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)

def rejected : Realization signature.{u, v} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u, v}
  Law r := ∀ {d : Type u} {n : Type v} [Fintype d] [DecidableEq d]
    [Fintype n] [DecidableEq n]
    (F : d → d → Matrix n n ℂ)
    (hmul : ∀ i j k l, F i j * F k l = if j = k then F i l else 0)
    (hstar : ∀ i j, (F i j)ᴴ = F j i) (v : d),
    (∑ b, (decoderKraus F v b)ᴴ * decoderKraus F v b) =
      unitSupport (r.readout () ⟨d, n⟩ F)

theorem actual_law : arena.{u, v}.Law actual := by
  intro d n _ _ _ _ F hmul hstar v
  exact decoder_kraus_gram F hmul hstar v

theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  let d := ULift.{u} (Fin 1)
  let n := ULift.{v} (Fin 1)
  let F : d → d → Matrix n n ℂ := fun _ _ => 1
  have hm : ∀ i j k l, F i j * F k l = if j = k then F i l else 0 := by
    intro i j k l
    simp [F, Subsingleton.elim j k]
  have hs : ∀ i j, (F i j)ᴴ = F j i := by intro i j; simp [F]
  have hb := h F hm hs (ULift.up 0)
  have hg := decoder_kraus_gram F hm hs (ULift.up 0)
  change (∑ b, (decoderKraus F (ULift.up 0) b)ᴴ * decoderKraus F (ULift.up 0) b) =
    unitSupport (0 : d → d → Matrix n n ℂ) at hb
  rw [hg] at hb
  have he := congrArg (fun M : Matrix n n ℂ => M (ULift.up 0) (ULift.up 0)) hb
  simpa [unitSupport, F] using he

def registration : Registration arena.{u, v} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} (Fin 1), ULift.{v} (Fin 1)⟩, 0,
      (fun _ _ _ _ => 1), ?_⟩
    intro h
    have he := congrArg (fun F => F (ULift.up 0) (ULift.up 0) (ULift.up 0) (ULift.up 0)) h
    exact zero_ne_one he

set_option trace.InformationRegistration.check true in
register_information_theorem _root_.D5.S3.Quantum.Recovery.MatrixUnitDecoder.decoder_kraus_gram
  in arena
  readout via (realize signature.{u, v} (fun _ _ x => x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Recovery.MatrixUnitDecoder
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg"]
      stateBinder := 6 }] })
  escape continues (open)

#print axioms registration

end Gram
namespace MatrixObservation

abbrev signature : Signature where
  Params := Type u
  State := fun n => Matrix n n ℂ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output := fun _ n => Matrix n n ℂ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro x; exact nomatch x⟩

def actual : Realization signature.{u} :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)

def zeroFamily : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def oneFamily : Realization signature.{u} :=
  realize signature (fun _ _ _ _ _ => 1) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨ULift.{u} (Fin 1), 0, (fun _ _ => 1), ?_⟩
  intro h
  have he := congrArg (fun M => M (ULift.up 0) (ULift.up 0)) h
  exact zero_ne_one he

end MatrixObservation

namespace Pairing
open MatrixObservation

abbrev arena : Arena where
  signature := signature.{v}
  Law r := ∀ {d : Type u} {n : Type v} [Fintype d] [DecidableEq d]
    [Fintype n] [DecidableEq n]
    (F : d → d → Matrix n n ℂ)
    (hmul : ∀ i j k l, F i j * F k l = if j = k then F i l else 0)
    (hstar : ∀ i j, (F i j)ᴴ = F j i) (v : d)
    (X : Matrix n n ℂ) (i j : d),
    (∑ b, decoderKraus F v b * X * (decoderKraus F v b)ᴴ) i j =
      Matrix.trace (F j i * r.readout () n X)

theorem actual_law : arena.{u, v}.Law actual := by
  intro d n _ _ _ _ F hmul hstar v X i j
  exact decoder_trace_pairing F hmul hstar v X i j

theorem rejected_law : ¬ arena.{u, v}.Law zeroFamily := by
  intro h
  let d := ULift.{u} (Fin 1)
  let n := ULift.{v} (Fin 1)
  let F : d → d → Matrix n n ℂ := fun _ _ => 1
  have hm : ∀ i j k l, F i j * F k l = if j = k then F i l else 0 := by
    intro i j k l
    simp [F, Subsingleton.elim j k]
  have hs : ∀ i j, (F i j)ᴴ = F j i := by intro i j; simp [F]
  have hb := h F hm hs (ULift.up 0) 1 (ULift.up 0) (ULift.up 0)
  have hg := decoder_trace_pairing F hm hs (ULift.up 0) 1 (ULift.up 0) (ULift.up 0)
  change _ = Matrix.trace (F (ULift.up 0) (ULift.up 0) * (0 : Matrix n n ℂ)) at hb
  rw [hg] at hb
  simpa [F, Matrix.trace] using hb

def registration : Registration arena.{u, v} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, zeroFamily, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨zeroFamily, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := dependence

set_option trace.InformationRegistration.check true in
register_information_theorem _root_.D5.S3.Quantum.Recovery.MatrixUnitDecoder.decoder_trace_pairing
  in arena
  readout via (realize signature.{v} (fun _ _ x => x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Recovery.MatrixUnitDecoder
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 10 }] })
  escape continues (open)

#print axioms registration
end Pairing

namespace Multiplication
open MatrixObservation

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {d : Type u} {n : Type v} [Fintype d] [DecidableEq d]
    [Fintype n] [DecidableEq n]
    (F : d → d → Matrix n n ℂ)
    (hmul : ∀ i j k l, F i j * F k l = if j = k then F i l else 0)
    (A B : Matrix d d ℂ),
    representedMatrix F A * representedMatrix F B =
      representedMatrix F (r.readout () d A * B)

theorem actual_law : arena.{u, v}.Law actual := by
  intro d n _ _ _ _ F hmul A B
  exact represented_matrix_mul F hmul A B

theorem rejected_law : ¬ arena.{u, v}.Law zeroFamily := by
  intro h
  let d := ULift.{u} (Fin 1)
  let n := ULift.{v} (Fin 1)
  let F : d → d → Matrix n n ℂ := fun _ _ => 1
  have hm : ∀ i j k l, F i j * F k l = if j = k then F i l else 0 := by
    intro i j k l
    simp [F, Subsingleton.elim j k]
  have hb := h F hm 1 1
  have he := congrArg (fun M : Matrix n n ℂ => M (ULift.up 0) (ULift.up 0)) hb
  simp [zeroFamily, realize, representedMatrix, F, Matrix.zero_apply] at he
  exact one_ne_zero he

def registration : Registration arena.{u, v} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, zeroFamily, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨zeroFamily, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := dependence

set_option trace.InformationRegistration.check true in
register_information_theorem _root_.D5.S3.Quantum.Recovery.MatrixUnitDecoder.represented_matrix_mul
  in arena
  readout via (realize signature.{u} (fun _ _ x => x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Recovery.MatrixUnitDecoder
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "fn", "arg"]
      stateBinder := 8 }] })
  escape continues (open)

#print axioms registration
end Multiplication

namespace Channel
open MatrixObservation

abbrev arena : Arena where
  signature := signature.{v}
  Law r := ∀ {d : Type u} {n : Type v} [Fintype d] [DecidableEq d]
    [Fintype n] [DecidableEq n]
    (F : d → d → Matrix n n ℂ)
    (hmul : ∀ i j k l, F i j * F k l = if j = k then F i l else 0)
    (hstar : ∀ i j, (F i j)ᴴ = F j i) (v : d),
    ∃ decoder : QuantumChannel n d, ∀ X : Matrix n n ℂ, ∀ i j : d,
      CStarMatrix.ofMatrix.symm
        (decoder.toCompletelyPositiveMap (CStarMatrix.ofMatrix (r.readout () n X))) i j =
      Matrix.trace (F j i * X) +
        Matrix.trace ((1 - unitSupport F) * X) * (Matrix.single v v (1 : ℂ)) i j

theorem actual_law : arena.{u, v}.Law actual := by
  intro d n _ _ _ _ F hmul hstar v
  exact matrix_unit_decoder_channel F hmul hstar v

theorem rejected_law : ¬ arena.{u, v}.Law zeroFamily := by
  intro h
  let d := ULift.{u} (Fin 1)
  let n := ULift.{v} (Fin 1)
  let F : d → d → Matrix n n ℂ := fun _ _ => 1
  have hm : ∀ i j k l, F i j * F k l = if j = k then F i l else 0 := by
    intro i j k l
    simp [F, Subsingleton.elim j k]
  have hs : ∀ i j, (F i j)ᴴ = F j i := by intro i j; simp [F]
  obtain ⟨decoder, hd⟩ := h F hm hs (ULift.up 0)
  have he := hd 1 (ULift.up 0) (ULift.up 0)
  change decoder.toCompletelyPositiveMap 0 (ULift.up 0) (ULift.up 0) = _ at he
  simp [map_zero, F, unitSupport, Matrix.trace] at he

def registration : Registration arena.{u, v} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, zeroFamily, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨zeroFamily, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := dependence

set_option trace.InformationRegistration.check true in
register_information_theorem _root_.D5.S3.Quantum.Recovery.MatrixUnitDecoder.matrix_unit_decoder_channel
  in arena
  readout via (realize signature.{v} (fun _ _ x => x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Recovery.MatrixUnitDecoder
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "body", "body", "body", "fn", "arg", "fn", "fn", "arg", "arg", "arg"]
      stateBinder := 11 }] })
  escape continues (open)

#print axioms registration
end Channel

namespace Recovery
open MatrixObservation

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {d : Type u} {n : Type v} [Fintype d] [DecidableEq d]
    [Fintype n] [DecidableEq n]
    (F : d → d → Matrix n n ℂ)
    (hmul : ∀ i j k l, F i j * F k l = if j = k then F i l else 0)
    (hstar : ∀ i j, (F i j)ᴴ = F j i) (v : d) (Q : Matrix n n ℂ)
    (hcomm : ∀ i j, Q * F i j = F i j * Q)
    (hsupport : unitSupport F * Q = Q) (htrace : Matrix.trace (F v v * Q) = 1),
    ∃ decoder : QuantumChannel n d, ∀ A : Matrix d d ℂ,
      CStarMatrix.ofMatrix.symm
        (decoder.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Q * representedMatrix F A))) =
          r.readout () d A

theorem actual_law : arena.{u, v}.Law actual := by
  intro d n _ _ _ _ F hmul hstar v Q hcomm hsupport htrace
  exact decoder_recovers_commutant_weight F hmul hstar v Q hcomm hsupport htrace

theorem rejected_law : ¬ arena.{u, v}.Law oneFamily := by
  intro h
  let d := ULift.{u} (Fin 1)
  let n := ULift.{v} (Fin 1)
  let F : d → d → Matrix n n ℂ := fun _ _ => 1
  have hm : ∀ i j k l, F i j * F k l = if j = k then F i l else 0 := by
    intro i j k l
    simp [F, Subsingleton.elim j k]
  have hs : ∀ i j, (F i j)ᴴ = F j i := by intro i j; simp [F]
  obtain ⟨decoder, hd⟩ := h F hm hs (ULift.up 0) 1
    (by intro i j; simp) (by simp [unitSupport, F]) (by simp [F, Matrix.trace])
  have he := congrArg (fun M : Matrix d d ℂ => M (ULift.up 0) (ULift.up 0)) (hd 0)
  have hz : (1 : Matrix n n ℂ) * representedMatrix F 0 = 0 := by
    simp [representedMatrix]
  rw [hz] at he
  change decoder.toCompletelyPositiveMap 0 (ULift.up 0) (ULift.up 0) = 1 at he
  simp [map_zero] at he

def registration : Registration arena.{u, v} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, oneFamily, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨oneFamily, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := dependence

set_option trace.InformationRegistration.check true in
register_information_theorem _root_.D5.S3.Quantum.Recovery.MatrixUnitDecoder.decoder_recovers_commutant_weight
  in arena
  readout via (realize signature.{u} (fun _ _ x => x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Recovery.MatrixUnitDecoder
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "body", "body", "arg"]
      stateBinder := 15 }] })
  escape continues (open)

#print axioms registration
end Recovery

end
end Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder
