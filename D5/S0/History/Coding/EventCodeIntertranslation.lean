/- GID: D5/S0/History/Coding/EventCodeIntertranslation
   generality: G
   mirror-B: D5/B/S0/History/Coding/EventCodeIntertranslation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove faithful event codes and intertranslate prime and marker implementations. -/

import D5.S0.History.HistoryCarrier
import D5.S0.History.PrimeSequenceCode

namespace D5.S0.History.Coding.EventCodeIntertranslation

open D5.S0.History.PrimeSequenceCode

/-- The frozen field encoder sends the empty history to the empty code. -/
@[simp] theorem encode_field_nil : encodeField [] = [] := by
  change (FreeMonoid.lift pairMarker) 1 = 1
  exact map_one _

/-- The frozen field encoder emits one two-marker pair at a time. -/
@[simp] theorem encode_field_cons (marker : Marker) (field : MarkerHistory) :
    encodeField (marker :: field) = pairMarker marker * encodeField field := by
  change (FreeMonoid.lift pairMarker) (FreeMonoid.of marker * field) =
    pairMarker marker * (FreeMonoid.lift pairMarker) field
  rw [map_mul, FreeMonoid.lift_eval_of]

/-- Decode one marker field and return the suffix following its `11` separator. -/
def decodeFieldPrefix : MarkerHistory -> Option (MarkerHistory × MarkerHistory)
  | .E₁ :: .E₁ :: rest => some ([], rest)
  | .E₀ :: .E₀ :: rest =>
      (decodeFieldPrefix rest).map fun decoded => (.E₀ :: decoded.1, decoded.2)
  | .E₀ :: .E₁ :: rest =>
      (decodeFieldPrefix rest).map fun decoded => (.E₁ :: decoded.1, decoded.2)
  | _ => none

/-- Prefix decoding is a left inverse to the literal field code followed by `11`. -/
theorem decode_field_prefix_encode (field suffix : MarkerHistory) :
    decodeFieldPrefix (encodeField field * fieldSeparator * suffix) =
      some (field, suffix) := by
  refine FreeMonoid.inductionOn' field ?_ ?_
  · change decodeFieldPrefix (Marker.E₁ :: Marker.E₁ :: suffix) = some ([], suffix)
    rfl
  · intro marker field ih
    have encode_of_mul :
        encodeField (FreeMonoid.of marker * field) =
          pairMarker marker * encodeField field :=
      encode_field_cons marker field
    rw [encode_of_mul]
    cases marker
    · change (decodeFieldPrefix (encodeField field * fieldSeparator * suffix)).map
        (fun decoded => (FreeMonoid.of Marker.E₀ * decoded.1, decoded.2)) =
          some (FreeMonoid.of Marker.E₀ * field, suffix)
      rw [ih]
      rfl
    · change (decodeFieldPrefix (encodeField field * fieldSeparator * suffix)).map
        (fun decoded => (FreeMonoid.of Marker.E₁ * decoded.1, decoded.2)) =
          some (FreeMonoid.of Marker.E₁ * field, suffix)
      rw [ih]
      rfl

/-- Decode the fixed-width opcode component used by `encodeEvent`. -/
def decodeOpcode : MarkerHistory -> Option Opcode
  | [.E₀, .E₀, .E₀, .E₀] => some .gen
  | [.E₀, .E₀, .E₀, .E₁] => some .enc
  | [.E₀, .E₀, .E₁, .E₀] => some .norm
  | [.E₀, .E₀, .E₁, .E₁] => some .decode
  | [.E₀, .E₁, .E₀, .E₀] => some .length
  | [.E₀, .E₁, .E₀, .E₁] => some .phase
  | [.E₀, .E₁, .E₁, .E₀] => some .read
  | [.E₀, .E₁, .E₁, .E₁] => some .ledger
  | [.E₁, .E₀, .E₀, .E₀] => some .renorm
  | [.E₁, .E₀, .E₀, .E₁] => some .complete
  | [.E₁, .E₀, .E₁, .E₀] => some .reflect
  | [.E₁, .E₀, .E₁, .E₁] => some .certify
  | _ => none

/-- The fixed-width opcode decoder recovers every repository opcode. -/
theorem decode_opcode_opcode_code (op : Opcode) :
    decodeOpcode (opcodeCode op) = some op := by
  cases op <;> rfl

/-- Decode the final one-marker tag field. -/
def decodeTag : MarkerHistory -> Option Marker
  | [.E₀, .E₀] => some .E₀
  | [.E₀, .E₁] => some .E₁
  | _ => none

/-- Decode a marker-level event code into its four components. -/
def decodeEventMarker (code : MarkerHistory) : Option Event := do
  let (src, afterSrc) <- decodeFieldPrefix code
  let (opCode, afterOp) <- decodeFieldPrefix afterSrc
  let op <- decodeOpcode opCode
  let (arg, tagCode) <- decodeFieldPrefix afterOp
  let tag <- decodeTag tagCode
  pure { src := src, op := op, arg := arg, tag := tag }

/-- The frozen event encoder is its four encoded fields separated by `11`. -/
theorem encode_event_expansion (event : Event) :
    encodeEvent event =
      encodeField event.src * fieldSeparator *
        (encodeField (opcodeCode event.op) * fieldSeparator *
          (encodeField event.arg * fieldSeparator *
            encodeField (FreeMonoid.of event.tag))) := by
  unfold encodeEvent
  have singleton_eq : ([event.tag] : MarkerHistory) = FreeMonoid.of event.tag :=
    FreeMonoid.ofList_singleton event.tag
  rw [singleton_eq]
  simp only [mul_assoc]

/-- Marker decoding recovers the event whose four components were encoded. -/
theorem decode_event_marker_encode (event : Event) :
    decodeEventMarker (encodeEvent event) = some event := by
  rcases event with ⟨src, op, arg, tag⟩
  rw [encode_event_expansion]
  simp only [decodeEventMarker]
  rw [decode_field_prefix_encode]
  change
    (do
      let (opCode, afterOp) <- decodeFieldPrefix
        (encodeField (opcodeCode op) * fieldSeparator *
          (encodeField arg * fieldSeparator * encodeField (FreeMonoid.of tag)))
      let decodedOp <- decodeOpcode opCode
      let (decodedArg, tagCode) <- decodeFieldPrefix afterOp
      let decodedTag <- decodeTag tagCode
      pure ({ src := src, op := decodedOp, arg := decodedArg, tag := decodedTag } : Event)) =
        some ({ src := src, op := op, arg := arg, tag := tag } : Event)
  rw [decode_field_prefix_encode]
  change
    (do
      let decodedOp <- decodeOpcode (opcodeCode op)
      let (decodedArg, tagCode) <- decodeFieldPrefix
        (encodeField arg * fieldSeparator * encodeField (FreeMonoid.of tag))
      let decodedTag <- decodeTag tagCode
      pure ({ src := src, op := decodedOp, arg := decodedArg, tag := decodedTag } : Event)) =
        some ({ src := src, op := op, arg := arg, tag := tag } : Event)
  rw [decode_opcode_opcode_code]
  change
    (do
      let (decodedArg, tagCode) <- decodeFieldPrefix
        (encodeField arg * fieldSeparator * encodeField (FreeMonoid.of tag))
      let decodedTag <- decodeTag tagCode
      pure ({ src := src, op := op, arg := decodedArg, tag := decodedTag } : Event)) =
        some ({ src := src, op := op, arg := arg, tag := tag } : Event)
  rw [decode_field_prefix_encode]
  cases tag <;> rfl

/-- The literal marker implementation `0 -> 00`, `1 -> 01`, separator `11`
is injective on event quadruples. -/
theorem encode_event_injective : Function.Injective encodeEvent := by
  intro first second equality
  have decoded := congrArg decodeEventMarker equality
  simpa only [decode_event_marker_encode, Option.some.injEq] using decoded

/-- Numeric digit assigned to each primitive marker. -/
def markerDigit : Marker -> Nat
  | .E₀ => 0
  | .E₁ => 1

/-- The primitive marker-to-digit map is injective. -/
theorem marker_digit_injective : Function.Injective markerDigit := by
  intro first second equality
  cases first <;> cases second <;> simp_all [markerDigit]

/-- Encode a marker history as its finite sequence of binary digits. -/
def markerDigits (history : MarkerHistory) : List Nat :=
  history.map markerDigit

/-- Binary digit lists faithfully retain marker histories. -/
theorem marker_digits_injective : Function.Injective markerDigits :=
  List.map_injective_iff.mpr marker_digit_injective

/-- Numeric index assigned to each member of the fixed instruction set. -/
def opcodeIndex : Opcode -> Nat
  | .gen => 0
  | .enc => 1
  | .norm => 2
  | .decode => 3
  | .length => 4
  | .phase => 5
  | .read => 6
  | .ledger => 7
  | .renorm => 8
  | .complete => 9
  | .reflect => 10
  | .certify => 11

/-- The opcode index is injective. -/
theorem opcode_index_injective : Function.Injective opcodeIndex := by
  intro first second equality
  cases first <;> cases second <;> simp_all [opcodeIndex]

/-- Definition 14.1's event quadruple after each component has received a
natural-number code. Source and argument histories use the frozen shifted
prime-sequence code for their binary digit lists. -/
noncomputable def eventComponentSequence (event : Event) : List Nat :=
  [primeSequenceCode (markerDigits event.src), opcodeIndex event.op,
    primeSequenceCode (markerDigits event.arg), markerDigit event.tag]

/-- The four-component natural sequence faithfully retains an event. -/
theorem event_component_sequence_injective :
    Function.Injective eventComponentSequence := by
  rintro ⟨firstSrc, firstOp, firstArg, firstTag⟩
    ⟨secondSrc, secondOp, secondArg, secondTag⟩ equality
  simp only [eventComponentSequence, List.cons.injEq] at equality
  rcases equality with ⟨srcEquality, opEquality, argEquality, tagEquality⟩
  have srcDigitsEquality := prime_sequence_code_injective srcEquality
  have argDigitsEquality := prime_sequence_code_injective argEquality
  have srcEquality' := marker_digits_injective srcDigitsEquality
  have argEquality' := marker_digits_injective argDigitsEquality
  have opEquality' := opcode_index_injective opEquality
  have tagEquality' := marker_digit_injective tagEquality.1
  subst secondSrc
  subst secondOp
  subst secondArg
  subst secondTag
  rfl

/-- Prime-power implementation of the event quadruple code. -/
noncomputable def eventPrimeCode (event : Event) : Nat :=
  primeSequenceCode (eventComponentSequence event)

/-- The prime-power event implementation is injective. -/
theorem event_prime_code_injective : Function.Injective eventPrimeCode := by
  intro first second equality
  apply event_component_sequence_injective
  exact prime_sequence_code_injective equality

/-- A concrete event witness supplies the nonempty domain needed by inverse-on-range maps. -/
instance eventNonempty : Nonempty Event :=
  ⟨{ src := 1, op := .gen, arg := 1, tag := .E₀ }⟩

/-- Translate a prime-power code to a marker code. Its specified behavior is
on the image of `eventPrimeCode`; outside that image `invFun` chooses a default. -/
noncomputable def primeToMarkerCode (code : Nat) : MarkerHistory :=
  encodeEvent (Function.invFun eventPrimeCode code)

/-- Translate a marker code to a prime-power code. Its specified behavior is
on the image of `encodeEvent`; outside that image `invFun` chooses a default. -/
noncomputable def markerToPrimeCode (code : MarkerHistory) : Nat :=
  eventPrimeCode (Function.invFun encodeEvent code)

/-- The prime-power and literal marker implementations intertranslate on every
encoded event, with genuinely distinct endpoints `Nat` and `MarkerHistory`. -/
theorem event_code_intertranslation (event : Event) :
    primeToMarkerCode (eventPrimeCode event) = encodeEvent event ∧
      markerToPrimeCode (encodeEvent event) = eventPrimeCode event := by
  constructor
  · change encodeEvent (Function.invFun eventPrimeCode (eventPrimeCode event)) = _
    rw [Function.leftInverse_invFun event_prime_code_injective event]
  · change eventPrimeCode (Function.invFun encodeEvent (encodeEvent event)) = _
    rw [Function.leftInverse_invFun encode_event_injective event]

#print axioms encode_field_nil
#print axioms encode_field_cons
#print axioms decodeFieldPrefix
#print axioms decode_field_prefix_encode
#print axioms decodeOpcode
#print axioms decode_opcode_opcode_code
#print axioms decodeTag
#print axioms decodeEventMarker
#print axioms encode_event_expansion
#print axioms decode_event_marker_encode
#print axioms encode_event_injective
#print axioms markerDigit
#print axioms marker_digit_injective
#print axioms markerDigits
#print axioms marker_digits_injective
#print axioms opcodeIndex
#print axioms opcode_index_injective
#print axioms eventComponentSequence
#print axioms event_component_sequence_injective
#print axioms eventPrimeCode
#print axioms event_prime_code_injective
#print axioms eventNonempty
#print axioms primeToMarkerCode
#print axioms markerToPrimeCode
#print axioms event_code_intertranslation

end D5.S0.History.Coding.EventCodeIntertranslation
