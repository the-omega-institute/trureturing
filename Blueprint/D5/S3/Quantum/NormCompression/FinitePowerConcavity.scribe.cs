using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.NormCompression;

internal sealed class FinitePowerConcavityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual finite power concavity on the full cone of nonnegative two row tables.",
        H("Finite two row power concavity"), Blocks(
            Describe.Lean(
                DescribeId.Create("finite-power-concaveon-fq"),
                DeclarationHandle.Create("D5/S3/Quantum/NormCompression/FinitePowerConcavity.concaveOn_Fq"),
                H("Concavity on the full nonnegative cone"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite column type and every real 1 < q < 2, Fq is concave on the entire nonnegative cone. The proof differentiates the actual operator trace in the positive definite chart, retains all three symmetric directions in the inverse metric, and passes to all boundary tables by the explicit two column regularization. The empty, singular and axial cases are included."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-power-fq-add-ge"),
                DeclarationHandle.Create("D5/S3/Quantum/NormCompression/FinitePowerConcavity.Fq_add_ge"),
                H("Superadditivity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Full cone concavity and degree one homogeneity imply Fq(W)+Fq(V) <= Fq(W+V) for all nonnegative finite tables."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-power-monotoneon-fq"),
                DeclarationHandle.Create("D5/S3/Quantum/NormCompression/FinitePowerConcavity.monotoneOn_Fq"),
                H("Entrywise monotonicity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For 1 < q < 2, entrywise order between nonnegative tables implies the same order between their actual Fq trace powers."))), DescribeRole.Theorem),
            Paragraph(Text("This supplier does not prove the original Audenaert inequality for arbitrary finite complex positive semidefinite block matrices. The separately proved local output compression budget consumes its full cone concavity. Classical Carlen-Lieb fixed invertible congruence convexity is a different statement and does not supply a substitute for this theorem.")))));
}
