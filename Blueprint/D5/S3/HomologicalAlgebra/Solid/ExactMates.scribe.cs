using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class ExactMatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compatibility of an exact adjunction and its mates with the unbounded derived localization. New proofs, released under the Apache 2.0 license. The localization constructions used here are Mathlib's proved constructions.",
        H("Exact Mates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-exactmates-exactadjunctionderived-unit-mate"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/ExactMates.exactAdjunctionDerived_unit_mate"),
                H("exact Adjunction Derived unit mate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A mate relation for an exact adjunction remains the same relation after unbounded derived localization. This is proved from the actual localized unit, rather than assumed as an additional adjunction compatibility.")),
                    Paragraph(Text("Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor provides NatTrans.mapDerivedCategory for natural transformations between additive functors preserving finite limits and finite colimits between abelian categories with derived categories. It descends the degreewise transformation through the unbounded quasi-isomorphism localization and commutes with integer shifts. Shift compatibility is transported through localization; no additional derived-existence hypothesis is introduced.")),
                    Paragraph(Text("For every integer-indexed complex X, NatTrans.mapDerivedCategory_app_Q_obj identifies the component of the localized transformation at Q(X) with the degreewise map conjugated by the two exact-functor localization comparisons. This formula supplies the mate and defining-cell compatibility used in the solid derived construction."))),
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
