using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class FiniteApproximationDescentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual free descent of representative differences along the full compact kernel pair, then through the protected infinity cokernel. Constructs P -> free(S), without any derived-adjunction/realization premise. New proofs, Apache-2.0; Juan Esteban Rodríguez Camargo, Notes on Solid Geometry, Lemma 3.3.2. Effective-epi proof pattern: immutable Apache-2.0 CWComparison.FreeCoverPresentation (2026); no supplier source is modified.",
        H("Finite Approximation Descent"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-finiteapproximationdescent-finiteapproximationfreedifference-relation"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/FiniteApproximationDescent.finiteApproximationFreeDifference_relation"),
                H("finite Approximation Free Difference relation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Equality on the entire relation follows from a genuine finite cover."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-finiteapproximationdescent-finiteapproximationfreesequence-infty"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/FiniteApproximationDescent.finiteApproximationFreeSequence_infty"),
                H("finite Approximation Free Sequence infty"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An actual infinity lift kills the infinity value of the descended sequence."))),
                DescribeRole.Theorem))));
}
