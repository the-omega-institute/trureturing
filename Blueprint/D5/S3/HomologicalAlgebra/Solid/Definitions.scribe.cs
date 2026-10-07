using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class DefinitionsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "# Derived solidification of free CW complexes This challenge is extracted from the LeanCondensed project <https://github.com/dagurtomas/LeanCondensed>, which develops the theory of light condensed mathematics of Clausen–Scholze in Lean. The target statement is the comparison theorem for a CW complex `X`: the homology of the derived solidification of the free light condensed abelian group on `X` is integral singular homology. The non-`sorry` part of this file develops, using only Mathlib, the definition of *light solid abelian groups*: a light condensed abelian group `A` is solid if the map `1 - shift` on the free light condensed abelian group `P = ℤ[ℕ∪{∞}]/ℤ[∞]` induces an isomorphism on internal homs into `A`. The full subcategory `Solid` of solid objects is closed under limits, kernels, cokernels and finite products, hence abelian, and the inclusion into light condensed abelian groups is exact, so it induces a functor on derived categories. The `sorry`ed declarations (the holes of this multi-hole problem) are: * `solidification` — the solidification functor `LightCondAb ⥤ Solid`; * `solidification_additive` — additivity of the solidification functor; * `solidificationAdjunction` — solidification is left adjoint to the inclusion; * `derivedSolidification` — the derived solidification functor `DerivedCategory LightCondAb ⥤ DerivedCategory Solid`; * `derivedSolidificationCounit` — the comparison map exhibiting `derivedSolidification` as a functor under degreewise solidification; * `derivedSolidification_isLeftDerivedFunctor` — `derivedSolidification` is the total left derived functor of degreewise solidification; * `derivedSolidificationAdjunction` — derived solidification is left adjoint to the derived inclusion; * `derivedSolidificationFreeCWFunctor` — the functor on CW complexes whose values are the derived inclusion of the derived solidification of the free light condensed abelian group; * `derivedSolidificationFreeCWFunctorSpec` — an isomorphism identifying `derivedSolidificationFreeCWFunctor` with the expected composite functor; * `derivedSolidification_free_CW_derivedNatIso` — naturally in a CW complex `X`, the derived inclusion of the derived solidification of `ℤ[X]` is isomorphic in the derived category of light condensed abelian groups to the integral singular chain complex of `X`, viewed as a complex of discrete light condensed abelian groups with homological degree `n` placed in cohomological degree `-n`, this is the main challenge; * `derivedSolidification_free_CW_homologyIso` — for a CW complex `X`, the homology of the derived solidification of `ℤ[X]` is integral singular homology (the derived category is cohomologically indexed, so the `n`-th singular homology group appears in degree `-n`); * `derivedSolidification_free_CW_homology` — the theorem form of the previous isomorphism. All holes must be filled compatibly: the adjunctions and derived functor property pin down `solidification` and `derivedSolidification` up to natural isomorphism, so the final derived comparison theorem and its pointwise homology form have their intended mathematical content. Note that the LeanCondensed project contains significant progress towards some of the earlier holes in this challenge.",
        H("Definitions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-definitions-p"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/Definitions.P"),
                H("P"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The light condensed abelian group `P = ℤ[ℕ∪{∞}]/ℤ[∞]`."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("solid-definitions-issolid"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/Definitions.isSolid"),
                H("is Solid"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A light condensed abelian group `A` is *solid* if the map `1 - shift` on `P` induces an isomorphism on internal homs into `A`."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("solid-definitions-solid"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/Definitions.Solid"),
                H("Solid"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The category of light solid abelian groups, as the full subcategory of solid objects in light condensed abelian groups."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("solid-definitions-derivedinclusion"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/Definitions.derivedInclusion"),
                H("derived Inclusion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact functor on derived categories induced by the inclusion `Solid ⥤ LightCondAb`."))),
                DescribeRole.Definition))));
}
