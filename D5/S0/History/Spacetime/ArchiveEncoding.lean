/- GID: D5/S0/History/Spacetime/ArchiveEncoding
   generality: G
   mirror-B: D5/B/S0/History/Spacetime/ArchiveEncoding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Contexts and selected histories correspond exactly to independently legal finite HF records. -/

import D5.S0.History.Spacetime.ArchiveRecordEncoding

set_option autoImplicit false

namespace D5.S0.History.Spacetime.ArchiveEncoding

open HFEncoding ArchiveCarrier FiniteGraphEncoding ArchiveRecordEncoding
noncomputable section

/-- Inclusion of literal HF event sets, independent of all typed encoders. -/
def Included (a b : HF) : Prop := ∀ x, mem x a → mem x b

/-- A context is a nested archive tuple and a current region contained in its event set. -/
def IsContextCode (d : Nat) (c : HF) : Prop :=
  ∃ E F R O, c = pair (pair E (pair F R)) O ∧
    Legal d ⟨members E, F, R⟩ ∧ Included O E

def contextCode {d : Nat} (c : Context d) : HF :=
  pair (archiveCode c.archive) (subsetCode c.archive.events c.current)

theorem contextCode_valid {d : Nat} (c : Context d) : IsContextCode d (contextCode c) := by
  refine ⟨setCode c.archive.events, (archiveRecord c.archive).attributes,
    (archiveRecord c.archive).causal, subsetCode c.archive.events c.current, rfl, ?_, ?_⟩
  · simpa [archiveRecord] using archiveRecord_legal c.archive
  · intro x hx
    exact (mem_setCode x _).mpr (subsetCode_valid _ _ x hx)

theorem contextCode_injective {d : Nat} : Function.Injective (@contextCode d) := by
  rintro ⟨a, s⟩ ⟨b, t⟩ h
  obtain ⟨ha, hs⟩ := pair_inj.mp h
  have hab : a = b := archiveCode_inj.mp ha
  subst b
  have hst : s = t := (subset_code_equiv a.events).injective (Subtype.ext hs)
  subst t
  rfl

/-- Legal graph reconstruction supplies all archived attributes and the current subset. -/
theorem contextCode_full {d : Nat} {c : HF} (h : IsContextCode d c) :
    ∃ a : Context d, contextCode a = c := by
  obtain ⟨E, F, R, O, rfl, h, hO⟩ := h
  have hs : IsSubsetCode (members E) O := fun x hx => mem_members.mpr (hO x hx)
  refine ⟨⟨reconstructArchive ⟨members E, F, R⟩ h, decodeSubset (members E) O⟩, ?_⟩
  change pair (recordCode (archiveRecord (reconstructArchive _ h)))
    (subsetCode (members E) (decodeSubset (members E) O)) = _
  rw [encode_reconstructArchive, encode_decodeSubset _ _ hs]
  simp [recordCode]

def context_code_equiv (d : Nat) : Context d ≃ {c // IsContextCode d c} :=
  Equiv.ofBijective (fun c => ⟨contextCode c, contextCode_valid c⟩)
    ⟨fun _ _ h => contextCode_injective (congrArg Subtype.val h), by
      rintro ⟨c, hc⟩
      obtain ⟨a, ha⟩ := contextCode_full hc
      exact ⟨a, Subtype.ext ha⟩⟩

def decodeContext {d : Nat} (c : HF) (h : IsContextCode d c) : Context d :=
  (context_code_equiv d).symm ⟨c, h⟩

@[simp] theorem decodeContext_encode {d : Nat} (c : Context d) :
    decodeContext (contextCode c) (contextCode_valid c) = c :=
  (context_code_equiv d).symm_apply_apply c

@[simp] theorem encode_decodeContext {d : Nat} (c : HF) (h : IsContextCode d c) :
    contextCode (decodeContext c h) = c :=
  congrArg Subtype.val ((context_code_equiv d).apply_symm_apply ⟨c, h⟩)

@[simp] theorem contextCode_inj {d : Nat} {a b : Context d} :
    contextCode a = contextCode b ↔ a = b := contextCode_injective.eq_iff

/-- The final selected set must lie in the current region, not merely in the archive. -/
def IsRichCode (d : Nat) (c : HF) : Prop :=
  ∃ E F R O A, c = pair (pair (pair E (pair F R)) O) A ∧
    Legal d ⟨members E, F, R⟩ ∧ Included O E ∧ Included A O

def richCode {d : Nat} (x : Rich d) : HF :=
  pair (contextCode x.1) (subsetCode x.1.archive.events x.2.val)

theorem richCode_valid {d : Nat} (x : Rich d) : IsRichCode d (richCode x) := by
  refine ⟨setCode x.1.archive.events, (archiveRecord x.1.archive).attributes,
    (archiveRecord x.1.archive).causal, subsetCode x.1.archive.events x.1.current,
    subsetCode x.1.archive.events x.2.val, rfl, ?_, ?_, ?_⟩
  · simpa [archiveRecord] using archiveRecord_legal x.1.archive
  · intro e he
    exact (mem_setCode e _).mpr (subsetCode_valid _ _ e he)
  · intro e he
    obtain ⟨a, ha, rfl⟩ := (mem_subsetCode _ _ e).mp he
    exact (event_mem_subsetCode _ _ a).mpr (x.2.property ha)

theorem richCode_injective {d : Nat} : Function.Injective (@richCode d) := by
  rintro ⟨c, a⟩ ⟨c', b⟩ h
  obtain ⟨hc, hs⟩ := pair_inj.mp h
  have hcc : c = c' := contextCode_injective hc
  subst c'
  have hab : a = b := Subtype.ext
    ((subset_code_equiv c.archive.events).injective (Subtype.ext hs))
  subst b
  rfl

/-- Both subset guards and all graph constraints survive reconstruction of a rich record. -/
theorem richCode_full {d : Nat} {c : HF} (h : IsRichCode d c) :
    ∃ x : Rich d, richCode x = c := by
  obtain ⟨E, F, R, O, A, rfl, h, hO, hA⟩ := h
  have hsO : IsSubsetCode (members E) O := fun x hx => mem_members.mpr (hO x hx)
  have hsA : IsSubsetCode (members E) A := fun x hx => mem_members.mpr (hO x (hA x hx))
  let ctx : Context d := ⟨reconstructArchive ⟨members E, F, R⟩ h, decodeSubset (members E) O⟩
  have hsel : decodeSubset (members E) A ⊆ ctx.current := by
    intro x hx
    exact (mem_decodeSubset _ _ x).mpr (hA x.val ((mem_decodeSubset _ _ x).mp hx))
  refine ⟨⟨ctx, ⟨decodeSubset (members E) A, hsel⟩⟩, ?_⟩
  change pair (pair (recordCode (archiveRecord (reconstructArchive _ h)))
    (subsetCode (members E) (decodeSubset (members E) O)))
    (subsetCode (members E) (decodeSubset (members E) A)) = _
  rw [encode_reconstructArchive, encode_decodeSubset _ _ hsO, encode_decodeSubset _ _ hsA]
  simp [recordCode]

def rich_code_equiv (d : Nat) : Rich d ≃ {c // IsRichCode d c} :=
  Equiv.ofBijective (fun x => ⟨richCode x, richCode_valid x⟩)
    ⟨fun _ _ h => richCode_injective (congrArg Subtype.val h), by
      rintro ⟨c, hc⟩
      obtain ⟨x, hx⟩ := richCode_full hc
      exact ⟨x, Subtype.ext hx⟩⟩

def decodeRich {d : Nat} (c : HF) (h : IsRichCode d c) : Rich d :=
  (rich_code_equiv d).symm ⟨c, h⟩

@[simp] theorem decodeRich_encode {d : Nat} (x : Rich d) :
    decodeRich (richCode x) (richCode_valid x) = x :=
  (rich_code_equiv d).symm_apply_apply x

@[simp] theorem encode_decodeRich {d : Nat} (c : HF) (h : IsRichCode d c) :
    richCode (decodeRich c h) = c :=
  congrArg Subtype.val ((rich_code_equiv d).apply_symm_apply ⟨c, h⟩)

@[simp] theorem richCode_inj {d : Nat} {x y : Rich d} :
    richCode x = richCode y ↔ x = y := richCode_injective.eq_iff

end
end D5.S0.History.Spacetime.ArchiveEncoding
