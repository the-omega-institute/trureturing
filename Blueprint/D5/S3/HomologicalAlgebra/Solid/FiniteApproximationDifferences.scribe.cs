using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class FiniteApproximationDifferencesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual compact light-profinite parameter space for the representative differences used in the generator retract. Every finite fiber is the stated pair of representatives, and every infinity fiber is diagonal. Projection onto the convergent sequence is surjective. No ordinary/derived free descent or realization is asserted in this topology module. New proofs, Apache-2.0; Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.2. The closure/fiber proof follows the accepted immutable CWComparison.BinaryEdgeSpace pattern; no frozen source is modified.",
        H("Finite Approximation Differences"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-finiteapproximationdifferences-finiteapproximationdifference-infty-fiber"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/FiniteApproximationDifferences.finiteApproximationDifference_infty_fiber"),
                H("finite Approximation Difference infty fiber"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. The actual compact light-profinite parameter space for the representative differences used in the generator retract. Every finite fiber is the stated pair of representatives, and every infinity fiber is diagonal. Projection onto the convergent sequence is surjective. No ordinary/derived free descent or realization is asserted in this topology module. New proofs, Apache-2.0; Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.2. The closure/fiber proof follows the accepted immutable CWComparison.BinaryEdgeSpace pattern; no frozen source is modified."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-finiteapproximationdifferences-finiteapproximationdifferenceprojection-surjective"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/FiniteApproximationDifferences.finiteApproximationDifferenceProjection_surjective"),
                H("finite Approximation Difference Projection surjective"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. The actual compact light-profinite parameter space for the representative differences used in the generator retract. Every finite fiber is the stated pair of representatives, and every infinity fiber is diagonal. Projection onto the convergent sequence is surjective. No ordinary/derived free descent or realization is asserted in this topology module. New proofs, Apache-2.0; Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.2. The closure/fiber proof follows the accepted immutable CWComparison.BinaryEdgeSpace pattern; no frozen source is modified."))),
                DescribeRole.Theorem))));
}
