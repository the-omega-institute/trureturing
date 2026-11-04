using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.NormCompression;

internal sealed class FinitePowerConcavityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual finite power concavity on the full cone of nonnegative two row tables.",
        H("Finite two row power concavity"), Blocks(
            Describe.Lean(
                DescribeId.Create("finite-power-boundarytable"),
                DeclarationHandle.Create("D5/S3/Quantum/NormCompression/FinitePowerConcavity.boundaryTable"),
                H("Regularizing boundary columns"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The appended table has columns epsilon (1,1) and epsilon (1,4). Its Aq columns are epsilon^(1/(2q)) (1,1) and epsilon^(1/(2q)) (1,4^(1/(2q)))."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-power-regularizedtable"),
                DeclarationHandle.Create("D5/S3/Quantum/NormCompression/FinitePowerConcavity.regularizedTable"),
                H("Positive regularization of the original table"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original columns receive epsilon in each entry, followed by the two explicit independent boundary columns. This construction retains the original finite column type and adds only two columns."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-power-boundary-gram-posdef"),
                DeclarationHandle.Create("D5/S3/Quantum/NormCompression/FinitePowerConcavity.boundary_gram_posDef"),
                H("Independent boundary columns"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive q and epsilon the actual boundary row Gram is positive definite."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-power-regularizedtable-pos"),
                DeclarationHandle.Create("D5/S3/Quantum/NormCompression/FinitePowerConcavity.regularizedTable_pos"),
                H("Strictly positive regularization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every entry is positive for positive epsilon and a nonnegative original table."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-power-regularized-gram-posdef"),
                DeclarationHandle.Create("D5/S3/Quantum/NormCompression/FinitePowerConcavity.regularized_gram_posDef"),
                H("Positive definite row Gram"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual regularized row Gram is positive definite, even when the original column type is empty."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-power-tendsto-regularized-fq"),
                DeclarationHandle.Create("D5/S3/Quantum/NormCompression/FinitePowerConcavity.tendsto_regularized_Fq"),
                H("Full boundary recovery"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual regularized Schatten trace power tends to the original Fq as epsilon tends to zero."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-power-fq-eq-two-eigenvalue-formula"),
                DeclarationHandle.Create("D5/S3/Quantum/NormCompression/FinitePowerConcavity.Fq_eq_two_eigenvalue_formula"),
                H("Exact two dimensional spectral chart"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For q positive and an entrywise nonnegative table, the explicit two eigenvalue formula equals the actual Schatten trace power. It includes singular and repeated eigenvalues."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-power-regularizedtable-affine"),
                DeclarationHandle.Create("D5/S3/Quantum/NormCompression/FinitePowerConcavity.regularizedTable_affine"),
                H("Affine regularization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Regularization commutes with every affine combination whose coefficients sum to one."))), DescribeRole.Theorem),
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
