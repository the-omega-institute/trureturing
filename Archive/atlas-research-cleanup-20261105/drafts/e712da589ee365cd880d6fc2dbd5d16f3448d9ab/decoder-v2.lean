import D5.S3.Combinatorics.CircularWords.PrescribedDeletionDistance
import D5.S3.Arith.Coding.ErrorErasureUniqueDecoding

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace R3Transient
open D5.S3.Combinatorics.CircularWords
open CircularDeletionTransport DeletionReadoutReconstruction PrescribedDeletionDistance
open D5.S3.Arith.Coding.ResidueCodeErrorDetection
open D5.S3.Arith.Coding.ErrorErasureUniqueDecoding
universe u
variable {α : Type u} [DecidableEq α]

-- Temporary application check only. Not proposed for library admission.
private theorem decoder_application_check {A J : Finset α} (hA : 4 ≤ A.card)
    (hJA : J ⊆ A) (hJ : 3 ≤ J.card) (t e : ℕ)
    (hbudget : 2 * t + e < J.card - 2)
    (E : Finset α) (hEJ : E ⊆ J) (hE : E.card ≤ e)
    (received : ReadoutSection A) (C : SupportedCircle A)
    (herrors : errorCount J E received C ≤ t) :
    ∃! D : SupportedCircle A, errorCount J E received D ≤ t := by
  classical
  let ι : Fin J.card ≃ J := J.equivFin.symm
  let encode : SupportedCircle A → Fin J.card → Cycle α :=
    fun D i => delete (ι i).1 D.1
  have transport (p : α → Prop) :
      (Finset.univ.filter fun i : Fin J.card => p (ι i).1).card =
        (J.filter p).card := by
    apply Finset.card_bij (fun i _ => (ι i).1)
    · intro i hi
      exact Finset.mem_filter.mpr ⟨(ι i).2, (Finset.mem_filter.mp hi).2⟩
    · intro i hi j hj he
      exact ι.injective (Subtype.ext he)
    · intro x hx
      let y : J := ⟨x, (Finset.mem_filter.mp hx).1⟩
      refine ⟨ι.symm y, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [y] using (Finset.mem_filter.mp hx).2
      · simp [y]
  have hdist (D F : SupportedCircle A) :
      hammingDist (encode D) (encode F) = readoutDistance J D F := by
    simpa only [hammingDist, encode, readoutDistance] using
      transport (fun x => delete x D.1 ≠ delete x F.1)
  have hinj : Function.Injective encode := by
    intro D F he
    by_contra hne
    have hl := (exact_prescribed_distance hA hJA hJ).1 D F hne
    have hz : readoutDistance J D F = 0 := by
      rw [← hdist D F, he]
      exact hammingDist_self _
    omega
  have hCode : MinDistanceAtLeast (Set.range encode) (J.card - 2) := by
    intro w hw v hv hne
    obtain ⟨D, rfl⟩ := hw
    obtain ⟨F, rfl⟩ := hv
    rw [hdist]
    apply (exact_prescribed_distance hA hJA hJ).1
    intro he
    exact hne (congrArg encode he)
  let erased : Finset (Fin J.card) := Finset.univ.filter fun i => (ι i).1 ∈ E
  have hEcard : erased.card = E.card := by
    change (Finset.univ.filter fun i : Fin J.card => (ι i).1 ∈ E).card = E.card
    calc
      _ = (J.filter fun x => x ∈ E).card := transport (fun x => x ∈ E)
      _ = E.card := by
        congr 1
        ext x
        simp only [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨hEJ h, h⟩⟩
  -- Erased coordinates are filled by the actual transmitted state's value.
  let filled : Fin J.card → Cycle α := fun i =>
    if (ι i).1 ∈ E then encode C i else (received (ι i).1).1
  have hcount (D : SupportedCircle A) :
      (Finset.univ.filter fun i => i ∉ erased ∧ filled i ≠ encode D i).card =
        errorCount J E received D := by
    calc
      _ = (Finset.univ.filter fun i : Fin J.card =>
          (ι i).1 ∉ E ∧ (received (ι i).1).1 ≠ delete (ι i).1 D.1).card := by
        congr 1
        ext i
        by_cases hi : (ι i).1 ∈ E <;> simp [erased, filled, encode, hi]
      _ = errorCount J E received D := by
        simpa only [errorCount] using
          transport (fun x => x ∉ E ∧ (received x).1 ≠ delete x D.1)
  have hTrueErrors :
      (Finset.univ.filter fun i => i ∉ erased ∧ filled i ≠ encode C i).card ≤ t := by
    rw [hcount]
    exact herrors
  have decoded := error_erasure_unique_decoding
    (α := Cycle α) (n := J.card) (d := J.card - 2) (e := t) (s := e)
    (C := Set.range encode) hCode erased (by omega) hbudget
    (encode C) filled ⟨C, rfl⟩ hTrueErrors
  obtain ⟨word, hw, hu⟩ := decoded
  obtain ⟨D, hD⟩ := hw.1
  refine ⟨D, ?_, ?_⟩
  · change errorCount J E received D ≤ t
    rw [← hcount D, hD]
    exact hw.2
  · intro F hF
    apply hinj
    have eqword := hu (encode F) ⟨⟨F, rfl⟩, by simpa only [hcount] using hF⟩
    exact eqword.trans hD.symm

-- Every legal partial tuple extends to the section carrier used above.
-- Same-label image membership is preserved even at every filled coordinate.
private theorem partial_section_extension {A J E : Finset α}
    (C : SupportedCircle A)
    (r : (x : {x : α // x ∈ J ∧ x ∉ E}) → ReadoutAlphabet A x.1) :
    ∃ s : ReadoutSection A, ∀ x (h : x ∈ J ∧ x ∉ E), s x = r ⟨x, h⟩ := by
  classical
  refine ⟨fun x => if h : x ∈ J ∧ x ∉ E then r ⟨x, h⟩
    else ⟨delete x C.1, ⟨C, rfl⟩⟩, ?_⟩
  intro x h
  simp [h]

#check @decoder_application_check
#print axioms decoder_application_check
#check @partial_section_extension
#print axioms partial_section_extension
end R3Transient
