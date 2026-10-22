/- GID: D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayEnumerator
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/GolayLeech/ExplicitGolayEnumerator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A faithful bitwise encoding gives the exact Golay weight enumerator. -/
import D5.S3.VertexAlgebra.GolayLeech.ExplicitGolayWeights

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace D5.S3.VertexAlgebra.GolayLeech.ExplicitGolayEnumerator

open ExplicitGolayCode ExplicitGolayCertificates ExplicitGolayWeights
open scoped BigOperators

def packedGenerator : Fin 12 → BitVec 24 :=
  ![8391395, 8394182, 8399756, 8410904, 8433200, 8477792,
    8566976, 8745344, 9102080, 9815552, 11242496, 14096384]

def decode (bits : BitVec 24) : Word :=
  fun axis => ((bits.getLsbD axis.val).toNat : Binary)

def packedWeight (bits : BitVec 24) : ℕ := ∑ axis : Fin 24, (bits.getLsbD axis.val).toNat

theorem decode_zero : decode 0 = 0 := by
  ext axis
  simp [decode]

theorem decode_xor (left right : BitVec 24) :
    decode (left ^^^ right) = decode left + decode right := by
  ext axis
  simp only [decode, BitVec.getLsbD_xor, Pi.add_apply]
  cases left_bit : left.getLsbD axis.val <;> cases right_bit : right.getLsbD axis.val <;> decide

theorem packed_generator_certificate : ∀ position : Fin 12,
    decode (packedGenerator position) = fun axis => generator axis position := by decide

def packedFrom : List (Fin 12) → Message → BitVec 24
  | [], _ => 0
  | position :: tail, message =>
      (if message position = 1 then packedGenerator position else 0) ^^^ packedFrom tail message

theorem decode_packedFrom (positions : List (Fin 12)) (message : Message) :
    decode (packedFrom positions message) =
      (positions.map (fun position => message position • (fun axis => generator axis position))).sum := by
  induction positions with
  | nil => simpa only [packedFrom, List.map_nil, List.sum_nil] using decode_zero
  | cons position tail induction_hypothesis =>
    rw [packedFrom, decode_xor, induction_hypothesis]
    simp only [List.map_cons, List.sum_cons]
    congr 1
    have selector : ∀ scalar : Binary,
        decode (if scalar = 1 then packedGenerator position else 0) =
          scalar • (fun axis => generator axis position) := by
      intro scalar
      have alternatives : scalar = 0 ∨ scalar = 1 := by
        fin_cases scalar
        · exact Or.inl rfl
        · exact Or.inr rfl
      rcases alternatives with rfl | rfl
      · rw [if_neg (by decide : (0 : Binary) ≠ 1), zero_smul]
        exact decode_zero
      · rw [if_pos rfl, one_smul]
        exact packed_generator_certificate position
    exact selector (message position)

def packedEncode (message : Message) : BitVec 24 :=
  packedFrom (List.ofFn (fun position : Fin 12 => position)) message

theorem packed_encode_identity (message : Message) : decode (packedEncode message) = encode message := by
  rw [packedEncode, decode_packedFrom]
  simp only [List.map_ofFn, Function.comp_def, List.sum_ofFn]
  ext axis
  simp [encode, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem packed_weight_identity (bits : BitVec 24) : weight (decode bits) = packedWeight bits := by
  apply Finset.sum_congr rfl
  intro axis _
  change (((bits.getLsbD axis.val).toNat : Binary).val) = (bits.getLsbD axis.val).toNat
  rw [ZMod.val_natCast]
  cases bits.getLsbD axis.val <;> rfl

def wordAt (pair : Fin 64 × Fin 64) : Word :=
  encode (joinedMessage (packedPrefix pair.1) (packedPrefix pair.2))

def bitsAt (pair : Fin 64 × Fin 64) : BitVec 24 :=
  packedEncode (joinedMessage (packedPrefix pair.1) (packedPrefix pair.2))

theorem word_weight_identity (pair : Fin 64 × Fin 64) :
    weight (wordAt pair) = packedWeight (bitsAt pair) := by
  rw [wordAt, ← packed_encode_identity, packed_weight_identity]
  rfl

theorem finite_prefix_injectivity : Function.Injective packedPrefix := by
  intro left right equal
  have checked : ∀ left right : Fin 64, packedPrefix left = packedPrefix right → left = right := by decide
  exact checked left right equal

theorem faithful_enumeration (word : Word) (member : word ∈ code) :
    ∃! pair : Fin 64 × Fin 64, wordAt pair = word := by
  obtain ⟨message, encoded⟩ := member
  let low : Fin 6 → Binary := fun position => message ⟨position.val, by omega⟩
  let high : Fin 6 → Binary := fun position => message ⟨position.val + 6, by omega⟩
  obtain ⟨left, left_equal⟩ := finite_prefix_surjectivity low
  obtain ⟨right, right_equal⟩ := finite_prefix_surjectivity high
  have recovered : joinedMessage (packedPrefix left) (packedPrefix right) = message := by
    rw [left_equal, right_equal]
    ext position
    fin_cases position <;> rfl
  refine ⟨(left, right), ?_, ?_⟩
  · change encode (joinedMessage (packedPrefix left) (packedPrefix right)) = word
    rw [recovered, encoded]
  · intro pair equality
    have messages_equal : joinedMessage (packedPrefix pair.1) (packedPrefix pair.2) = message :=
      encode_injective (equality.trans encoded.symm)
    apply Prod.ext
    · apply finite_prefix_injectivity
      rw [left_equal]
      ext position
      have component := congrFun messages_equal ⟨position.val, by omega⟩
      simpa [joinedMessage, low] using component
    · apply finite_prefix_injectivity
      rw [right_equal]
      ext position
      have component := congrFun messages_equal ⟨position.val + 6, by omega⟩
      simpa [joinedMessage, high, show ¬position.val + 6 < 6 by omega] using component

def weightValues : Fin 5 → ℕ := ![0, 8, 12, 16, 24]

def enumerate (category : Fin 5) : ℕ :=
  ∑ lower : Fin 64, ∑ upper : Fin 64,
    if weight (wordAt (lower, upper)) = weightValues category then 1 else 0

def packedEnumerateRow (lower : Fin 64) (category : Fin 5) : ℕ :=
  ∑ upper : Fin 64, if packedWeight (bitsAt (lower, upper)) = weightValues category then 1 else 0

def rowCertificate : Matrix (Fin 64) (Fin 5) ℕ :=
  !![  1, 45, 18, 0, 0;
  0, 9, 46, 9, 0;
  0, 19, 42, 3, 0;
  0, 9, 46, 9, 0;
  0, 19, 42, 3, 0;
  0, 1, 30, 33, 0;
  0, 19, 42, 3, 0;
  0, 9, 46, 9, 0;
  0, 19, 42, 3, 0;
  0, 1, 30, 33, 0;
  0, 3, 42, 19, 0;
  0, 1, 30, 33, 0;
  0, 19, 42, 3, 0;
  0, 1, 30, 33, 0;
  0, 19, 42, 3, 0;
  0, 9, 46, 9, 0;
  0, 19, 42, 3, 0;
  0, 9, 46, 9, 0;
  0, 3, 42, 19, 0;
  0, 9, 46, 9, 0;
  0, 3, 42, 19, 0;
  0, 1, 30, 33, 0;
  0, 3, 42, 19, 0;
  0, 9, 46, 9, 0;
  0, 19, 42, 3, 0;
  0, 9, 46, 9, 0;
  0, 3, 42, 19, 0;
  0, 9, 46, 9, 0;
  0, 19, 42, 3, 0;
  0, 9, 46, 9, 0;
  0, 19, 42, 3, 0;
  0, 33, 30, 1, 0;
  0, 33, 30, 1, 0;
  0, 19, 42, 3, 0;
  0, 9, 46, 9, 0;
  0, 19, 42, 3, 0;
  0, 9, 46, 9, 0;
  0, 3, 42, 19, 0;
  0, 9, 46, 9, 0;
  0, 19, 42, 3, 0;
  0, 9, 46, 9, 0;
  0, 3, 42, 19, 0;
  0, 1, 30, 33, 0;
  0, 3, 42, 19, 0;
  0, 9, 46, 9, 0;
  0, 3, 42, 19, 0;
  0, 9, 46, 9, 0;
  0, 19, 42, 3, 0;
  0, 33, 30, 1, 0;
  0, 3, 42, 19, 0;
  0, 9, 46, 9, 0;
  0, 3, 42, 19, 0;
  0, 9, 46, 9, 0;
  0, 0, 18, 45, 1;
  0, 9, 46, 9, 0;
  0, 3, 42, 19, 0;
  0, 33, 30, 1, 0;
  0, 3, 42, 19, 0;
  0, 9, 46, 9, 0;
  0, 3, 42, 19, 0;
  0, 33, 30, 1, 0;
  0, 3, 42, 19, 0;
  0, 33, 30, 1, 0;
  0, 19, 42, 3, 0]

end D5.S3.VertexAlgebra.GolayLeech.ExplicitGolayEnumerator
