using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.NormCompression;

internal sealed class FinitePowerSpectralDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact spectral chart and full boundary regularization for finite two row trace powers.",
        H("Two eigenvalue chart and boundary regularization"), Blocks(
            Describe.Lean(
                DescribeId.Create("finite-power-boundarytable"),
                DeclarationHandle.Create("D5/S3/Quantum/NormCompression/FinitePowerSpectral.boundaryTable"),
                H("Regularizing boundary columns"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The appended table has columns epsilon (1,1) and epsilon (1,4). Its Aq columns are epsilon^(1/(2q)) (1,1) and epsilon^(1/(2q)) (1,4^(1/(2q)))."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-power-regularizedtable"),
                DeclarationHandle.Create("D5/S3/Quantum/NormCompression/FinitePowerSpectral.regularizedTable"),
                H("Positive regularization of the original table"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original columns receive epsilon in each entry, followed by the two explicit independent boundary columns. This construction retains the original finite column type and adds only two columns."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-power-boundary-gram-posdef"),
                DeclarationHandle.Create("D5/S3/Quantum/NormCompression/FinitePowerSpectral.boundary_gram_posDef"),
                H("Independent boundary columns"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive q and epsilon the actual boundary row Gram is positive definite."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-power-regularizedtable-pos"),
                DeclarationHandle.Create("D5/S3/Quantum/NormCompression/FinitePowerSpectral.regularizedTable_pos"),
                H("Strictly positive regularization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every entry is positive for positive epsilon and a nonnegative original table."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-power-regularized-gram-posdef"),
                DeclarationHandle.Create("D5/S3/Quantum/NormCompression/FinitePowerSpectral.regularized_gram_posDef"),
                H("Positive definite row Gram"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual regularized row Gram is positive definite, even when the original column type is empty."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-power-tendsto-regularized-fq"),
                DeclarationHandle.Create("D5/S3/Quantum/NormCompression/FinitePowerSpectral.tendsto_regularized_Fq"),
                H("Full boundary recovery"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual regularized Schatten trace power tends to the original Fq as epsilon tends to zero."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-power-fq-eq-two-eigenvalue-formula"),
                DeclarationHandle.Create("D5/S3/Quantum/NormCompression/FinitePowerSpectral.Fq_eq_two_eigenvalue_formula"),
                H("Exact two dimensional spectral chart"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For q positive and an entrywise nonnegative table, the explicit two eigenvalue formula equals the actual Schatten trace power. It includes singular and repeated eigenvalues."))), DescribeRole.Theorem),
            Paragraph(Text("All formulas identify the actual operator trace; no curvature premise is assumed.")))));
}
