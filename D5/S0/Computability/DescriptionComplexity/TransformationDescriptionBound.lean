/- GID: D5/S0/Computability/DescriptionComplexity/TransformationDescriptionBound
   generality: G
   mirror-B: D5/B/S0/Computability/DescriptionComplexity/TransformationDescriptionBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A compiler bounds target description cost by source and transformation costs. -/

import Mathlib.Data.Nat.Find

namespace D5.S0.Computability.DescriptionComplexity.TransformationDescriptionBound

/-- A description system with a natural-number code cost. The encoder ensures
that every object has at least one realizing code. -/
structure DescriptionSystem (Object Code : Type*) where
  realizes : Code -> Object -> Prop
  codeCost : Code -> Nat
  encode : Object -> Code
  encode_realizes : forall object, realizes (encode object) object

private theorem costExists {Object Code : Type*}
    (system : DescriptionSystem Object Code) (object : Object) :
    exists cost, exists code,
      system.realizes code object /\ system.codeCost code = cost :=
  ⟨system.codeCost (system.encode object), system.encode object,
    system.encode_realizes object, rfl⟩

/-- The minimum cost of a code realizing an object. -/
noncomputable def descriptionComplexity {Object Code : Type*}
    (system : DescriptionSystem Object Code) (object : Object) : Nat := by
  classical
  exact Nat.find (costExists system object)

private theorem shortestCode {Object Code : Type*}
    (system : DescriptionSystem Object Code) (object : Object) :
    exists code, system.realizes code object /\
      system.codeCost code = descriptionComplexity system object := by
  classical
  exact Nat.find_spec (costExists system object)

/-- A fixed-overhead compiler that combines a transformation description with
a source description and preserves the declared application relation. -/
structure TransformationCompiler
    {Object Transformation SourceCode TransformationCode TargetCode : Type*}
    (source : DescriptionSystem Object SourceCode)
    (transformations : DescriptionSystem Transformation TransformationCode)
    (target : DescriptionSystem Object TargetCode)
    (applies : Transformation -> Object -> Object -> Prop)
    (overhead : Nat) where
  combine : TransformationCode -> SourceCode -> TargetCode
  combine_realizes : forall {transformation sourceObject targetObject}
      {transformationCode sourceCode},
    transformations.realizes transformationCode transformation ->
    source.realizes sourceCode sourceObject ->
    applies transformation sourceObject targetObject ->
    target.realizes (combine transformationCode sourceCode) targetObject
  combine_cost_le : forall transformationCode sourceCode,
    target.codeCost (combine transformationCode sourceCode) <=
      source.codeCost sourceCode +
        transformations.codeCost transformationCode + overhead

/-- Applying a described transformation increases minimum description cost by
at most the transformation cost and the compiler overhead. -/
theorem transformation_description_complexity_le
    {Object Transformation SourceCode TransformationCode TargetCode : Type*}
    {source : DescriptionSystem Object SourceCode}
    {transformations : DescriptionSystem Transformation TransformationCode}
    {target : DescriptionSystem Object TargetCode}
    {applies : Transformation -> Object -> Object -> Prop}
    {overhead : Nat}
    (compiler : TransformationCompiler source transformations target applies overhead)
    {transformation sourceObject targetObject}
    (happly : applies transformation sourceObject targetObject) :
    descriptionComplexity target targetObject <=
      descriptionComplexity source sourceObject +
        descriptionComplexity transformations transformation + overhead := by
  classical
  obtain ⟨sourceCode, hsource, hsourceCost⟩ := shortestCode source sourceObject
  obtain ⟨transformationCode, htransformation, htransformationCost⟩ :=
    shortestCode transformations transformation
  calc
    descriptionComplexity target targetObject <=
        target.codeCost (compiler.combine transformationCode sourceCode) := by
      unfold descriptionComplexity
      apply Nat.find_min'
      exact ⟨compiler.combine transformationCode sourceCode,
        compiler.combine_realizes htransformation hsource happly, rfl⟩
    _ <= source.codeCost sourceCode +
        transformations.codeCost transformationCode + overhead :=
      compiler.combine_cost_le transformationCode sourceCode
    _ = descriptionComplexity source sourceObject +
        descriptionComplexity transformations transformation + overhead := by
      rw [hsourceCost, htransformationCost]

private def naturalDescriptions : DescriptionSystem Nat Nat where
  realizes code object := code = object
  codeCost := id
  encode := id
  encode_realizes := fun _ => rfl

private def additionCompiler :
    TransformationCompiler naturalDescriptions naturalDescriptions
      naturalDescriptions (fun increment source target => target = source + increment) 0 where
  combine incrementCode sourceCode := sourceCode + incrementCode
  combine_realizes := by
    intro increment source target incrementCode sourceCode hincrement hsource happly
    dsimp [naturalDescriptions] at hincrement hsource ⊢
    subst incrementCode
    subst sourceCode
    exact happly.symm
  combine_cost_le := by
    intro incrementCode sourceCode
    simp [naturalDescriptions]

/-- Natural-number descriptions and addition give an inhabited positive-cost
instance of the transformation bound. -/
example :
    descriptionComplexity naturalDescriptions 5 <=
      descriptionComplexity naturalDescriptions 3 +
        descriptionComplexity naturalDescriptions 2 + 0 := by
  exact transformation_description_complexity_le additionCompiler
    (transformation := 2) (sourceObject := 3) (targetObject := 5) rfl

end D5.S0.Computability.DescriptionComplexity.TransformationDescriptionBound
