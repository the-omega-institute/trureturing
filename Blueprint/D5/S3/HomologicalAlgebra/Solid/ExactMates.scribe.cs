using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class ExactMatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compatibility of an exact adjunction and its mates with the unbounded derived localization. New proofs, released under the Apache 2.0 license. The localization constructions used here are Mathlib's proved constructions.",
        H("Exact Mates"),
        Blocks(
            Paragraph(Text("The degreewise composition comparison is supplied directly by Mathlib's Functor.mapHomologicalComplexCompIso under zero-morphism-preservation assumptions. Derived natural transformations, their shift compatibility and the complex-representative formula are supplied by Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor.")),
            Describe.Lean(
                DescribeId.Create("solid-exactmates-exactadjunctionderived-unit-mate"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/ExactMates.exactAdjunctionDerived_unit_mate"),
                H("exact Adjunction Derived unit mate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A mate relation for an exact adjunction remains the same relation after unbounded derived localization. This is proved from the actual localized unit, rather than assumed as an additional adjunction compatibility."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-exactmates-exactadjunctionderived-homequiv-mate"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/ExactMates.exactAdjunctionDerived_homEquiv_mate"),
                H("exact Adjunction Derived hom Equiv mate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the localized exact adjunction, precomposition by the left mate is postcomposition by the right mate. All derived objects are unbounded."))),
                DescribeRole.Theorem))));
}
