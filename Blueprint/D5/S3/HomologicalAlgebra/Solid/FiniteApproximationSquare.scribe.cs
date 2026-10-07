using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class FiniteApproximationSquareDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual representative-difference square. Its map into the compact parameter cover is continuous and lands in its full closure by density of finite rows. Thus equality is of condensed morphisms, not merely finite-point values. The zeroth row retains the finite initial quotient. New proofs, Apache-2.0; Rodríguez Camargo, Notes on Solid Geometry, Lemma 3.3.2.",
        H("Finite Approximation Square"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-finiteapproximationsquare-finiteapproximationshiftprevious"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/FiniteApproximationSquare.finiteApproximationShiftPrevious"),
                H("finite Approximation Shift Previous"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The predecessor cancels the protected successor shift, including infinity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-finiteapproximationsquare-finiteapproximationcoefficient-numerator-square"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/FiniteApproximationSquare.finiteApproximationCoefficient_numerator_square"),
                H("finite Approximation Coefficient numerator square"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The free coefficient map factors through the genuine descended sequence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-finiteapproximationsquare-finiteapproximationremainder-square"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/FiniteApproximationSquare.finiteApproximationRemainder_square"),
                H("finite Approximation Remainder square"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual finite-difference square, in the original ordinary category."))),
                DescribeRole.Theorem))));
}
