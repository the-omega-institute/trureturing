/- GID: D5/S0/Computability/DescriptionComplexity/XorTransformationTightness
   generality: G
   mirror-B: D5/B/S0/Computability/DescriptionComplexity/XorTransformationTightness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Binary XOR transformation prices are tight within an explicit logarithmic gap. -/

import Mathlib
import D5.S0.Computability.DescriptionComplexity.TransformationDescriptionBound

namespace D5.S0.Computability.DescriptionComplexity.XorTransformationTightness

open D5.S0.Computability.DescriptionComplexity.TransformationDescriptionBound

/-- Pointwise binary XOR on fixed-length strings, expressed as addition in `Fin 2`. -/
def pointwiseXor {length : Nat} (mask input : Fin length -> Fin 2) : Fin length -> Fin 2 :=
  fun i => input i + mask i

/-- The source-semantic interface supplied by one fixed binary description machine: object and
transformation descriptions use binary programs, application is compiled with fixed overhead,
and the concrete zero-string and XOR compilers have their standard costs. -/
structure BinaryDescriptionMachine (overhead : Nat) where
  objects : (length : Nat) -> DescriptionSystem (Fin length -> Fin 2) (List (Fin 2))
  transformations : (length : Nat) ->
    DescriptionSystem ((Fin length -> Fin 2) -> (Fin length -> Fin 2)) (List (Fin 2))
  object_cost : forall length code, (objects length).codeCost code = code.length
  transformation_cost : forall length code,
    (transformations length).codeCost code = code.length
  object_realizes_functional : forall {length code x y},
    (objects length).realizes code x -> (objects length).realizes code y -> x = y
  xorCode : forall {length}, (Fin length -> Fin 2) -> List (Fin 2)
  xorCode_realizes : forall {length} mask,
    (transformations length).realizes (xorCode mask) (pointwiseXor mask)
  xorCode_length_le : forall {length} (mask : Fin length -> Fin 2),
    (xorCode mask).length <= length + overhead
  zeroCode : (length : Nat) -> List (Fin 2)
  zeroCode_realizes : forall length,
    (objects length).realizes (zeroCode length) (0 : Fin length -> Fin 2)
  zeroCode_length_le : forall length,
    (zeroCode length).length <= 2 * Nat.log 2 (length + 1) + overhead
  applicationCompiler : forall length,
    TransformationCompiler (objects length) (transformations length) (objects length)
      (fun transformation source target => target = transformation source) overhead

private theorem shortest_code {Object Code : Type*}
    (system : DescriptionSystem Object Code) (object : Object) :
    exists code, system.realizes code object /\
      system.codeCost code = descriptionComplexity system object := by
  classical
  let costExists : exists cost, exists code,
      system.realizes code object /\ system.codeCost code = cost :=
    ⟨system.codeCost (system.encode object), system.encode object,
      system.encode_realizes object, rfl⟩
  simpa only [descriptionComplexity] using Nat.find_spec costExists

private theorem descriptionComplexity_le_code_cost {Object Code : Type*}
    (system : DescriptionSystem Object Code) {object : Object} {code : Code}
    (hrealizes : system.realizes code object) :
    descriptionComplexity system object <= system.codeCost code := by
  classical
  change Nat.find _ <= system.codeCost code
  apply Nat.find_min'
  exact ⟨code, hrealizes, rfl⟩

private theorem short_binary_programs_card (length : Nat) :
    Fintype.card (Sigma fun k : Fin length => Fin k.1 -> Fin 2) = 2 ^ length - 1 := by
  induction length with
  | zero => simp
  | succ length ih =>
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fun, Fintype.card_fin]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, Fin.val_succ]
    have hsum : (∑ i : Fin length, 2 ^ (i : Nat)) = 2 ^ length - 1 := by
      simpa [Fintype.card_sigma] using ih
    rw [show (∑ i : Fin length, 2 ^ ((i : Nat) + 1)) =
        (∑ i : Fin length, 2 ^ (i : Nat)) * 2 by
      simp [pow_succ, Finset.sum_mul]]
    rw [hsum, pow_succ]
    have hpow : 0 < 2 ^ length := pow_pos (by decide) length
    omega

private theorem exists_incompressible
    {overhead : Nat} (machine : BinaryDescriptionMachine overhead) (length : Nat) :
    exists word : Fin length -> Fin 2,
      length <= descriptionComplexity (machine.objects length) word := by
  classical
  by_contra hnone
  push Not at hnone
  have hshort : forall word : Fin length -> Fin 2,
      descriptionComplexity (machine.objects length) word < length := hnone
  let chosenCode (word : Fin length -> Fin 2) : List (Fin 2) :=
    Classical.choose (shortest_code (machine.objects length) word)
  have chosenCode_realizes (word : Fin length -> Fin 2) :
      (machine.objects length).realizes (chosenCode word) word :=
    (Classical.choose_spec (shortest_code (machine.objects length) word)).1
  have chosenCode_cost (word : Fin length -> Fin 2) :
      (machine.objects length).codeCost (chosenCode word) =
        descriptionComplexity (machine.objects length) word :=
    (Classical.choose_spec (shortest_code (machine.objects length) word)).2
  have chosenCode_length (word : Fin length -> Fin 2) :
      (chosenCode word).length < length := by
    rw [← machine.object_cost, chosenCode_cost]
    exact hshort word
  let shortCode := {code : List (Fin 2) // code.length < length}
  let chosenShort : (Fin length -> Fin 2) -> shortCode := fun word =>
    ⟨chosenCode word, chosenCode_length word⟩
  have chosenShort_injective : Function.Injective chosenShort := by
    intro x y hxy
    apply machine.object_realizes_functional (chosenCode_realizes x)
    have hcode : chosenCode x = chosenCode y := congrArg Subtype.val hxy
    rw [hcode]
    exact chosenCode_realizes y
  let packedShort := Sigma fun k : Fin length => Fin k.1 -> Fin 2
  let pack : shortCode -> packedShort := fun code =>
    ⟨⟨code.1.length, code.2⟩, code.1.get⟩
  have pack_injective : Function.Injective pack := by
    intro x y hxy
    apply Subtype.ext
    have hlists := congrArg (fun packed : packedShort => List.ofFn packed.2) hxy
    simpa [pack] using hlists
  letI : Finite shortCode := Finite.of_injective pack pack_injective
  have hobjects : Nat.card (Fin length -> Fin 2) = 2 ^ length := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun]
    simp
  have hpacked : Nat.card packedShort = 2 ^ length - 1 := by
    rw [Nat.card_eq_fintype_card]
    exact short_binary_programs_card length
  have hcard : Nat.card (Fin length -> Fin 2) <= Nat.card shortCode :=
    Nat.card_le_card_of_injective chosenShort chosenShort_injective
  have hshortCard : Nat.card shortCode <= Nat.card packedShort :=
    Nat.card_le_card_of_injective pack pack_injective
  rw [hobjects] at hcard
  rw [hpacked] at hshortCard
  have hpow : 0 < 2 ^ length := pow_pos (by decide) length
  omega

/-- For every length, an incompressible mask makes pointwise XOR attain the transformation
description bound within an explicit logarithmic gap. The statement publicly exposes the mask,
the canonical involution and its computation at the zero string, the information difference,
and both sides of the transformation-description squeeze. -/
theorem xor_transformation_description_tight
    {overhead : Nat} (machine : BinaryDescriptionMachine overhead) (length : Nat) :
    exists mask : Fin length -> Fin 2,
      length <= descriptionComplexity (machine.objects length) mask /\
      Function.Involutive (pointwiseXor mask) /\
      pointwiseXor mask 0 = mask /\
      length - (2 * Nat.log 2 (length + 1) + overhead) <=
        descriptionComplexity (machine.objects length) mask -
          descriptionComplexity (machine.objects length) 0 /\
      descriptionComplexity (machine.transformations length) (pointwiseXor mask) <=
        length + overhead /\
      length - (2 * Nat.log 2 (length + 1) + overhead + overhead) <=
        descriptionComplexity (machine.transformations length) (pointwiseXor mask) := by
  obtain ⟨mask, hmask⟩ := exists_incompressible machine length
  have hinvolutive : Function.Involutive (pointwiseXor mask) := by
    intro input
    funext i
    let bit := mask i
    change input i + bit + bit = input i
    have hbit : bit = 0 ∨ bit = 1 := by omega
    rcases hbit with hbit | hbit
    · simp [hbit]
    · have hinput : input i = 0 ∨ input i = 1 := by omega
      rcases hinput with hinput | hinput <;> rw [hbit, hinput] <;> decide
  have hzeroXor : pointwiseXor mask 0 = mask := by
    funext i
    simp [pointwiseXor]
  have hzero : descriptionComplexity (machine.objects length) (0 : Fin length -> Fin 2) <=
      2 * Nat.log 2 (length + 1) + overhead := by
    calc
      descriptionComplexity (machine.objects length) (0 : Fin length -> Fin 2) <=
          (machine.objects length).codeCost (machine.zeroCode length) :=
        descriptionComplexity_le_code_cost _ (machine.zeroCode_realizes length)
      _ = (machine.zeroCode length).length := machine.object_cost _ _
      _ <= 2 * Nat.log 2 (length + 1) + overhead := machine.zeroCode_length_le length
  have hxor : descriptionComplexity (machine.transformations length) (pointwiseXor mask) <=
      length + overhead := by
    calc
      descriptionComplexity (machine.transformations length) (pointwiseXor mask) <=
          (machine.transformations length).codeCost (machine.xorCode mask) :=
        descriptionComplexity_le_code_cost _ (machine.xorCode_realizes mask)
      _ = (machine.xorCode mask).length := machine.transformation_cost _ _
      _ <= length + overhead := machine.xorCode_length_le mask
  have happly : descriptionComplexity (machine.objects length) mask <=
      descriptionComplexity (machine.objects length) 0 +
        descriptionComplexity (machine.transformations length) (pointwiseXor mask) + overhead := by
    apply transformation_description_complexity_le (machine.applicationCompiler length)
    exact hzeroXor.symm
  refine ⟨mask, hmask, hinvolutive, hzeroXor, ?_, hxor, ?_⟩ <;> omega

#print axioms xor_transformation_description_tight

end D5.S0.Computability.DescriptionComplexity.XorTransformationTightness
