using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class OriginalSignedPrimeFourierDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaBridge/OriginalSignedPrimeFourier.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The negative actual symmetric von Mangoldt action is expanded on arbitrary finite signed mode sets with arbitrary complex coefficients. Both translations and all prime powers remain. The inclusive q=c row is zero only after compression, including c=5041=71 squared. This component supplies no full Weil positivity or numerical five-mode certificate.",
        H("Original Signed Prime Fourier"),
        Blocks(
                Paragraph(Text("The negative actual symmetric von Mangoldt action is expanded on arbitrary finite signed mode sets with arbitrary complex coefficients. Both translations and all prime powers remain. The inclusive q=c row is zero only after compression, including c=5041=71 squared. This component supplies no full Weil positivity or numerical five-mode certificate.")),
                Describe.Lean(DescribeId.Create("head"),
                    DeclarationHandle.Create(Owner + "head"), H("head"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The finite sum ranges over an arbitrary Finset of signed integers, with arbitrary complex coefficients and no even or real restriction."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("prime-matrix"),
                    DeclarationHandle.Create(Owner + "primeMatrix"), H("primeMatrix"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The signed matrix is negative the existing primeWeight-weighted sum of the two evaluated complex compression matrices. Every inclusive prime-power row is kept."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("finite-signed-prime-identity"),
                    DeclarationHandle.Create(Owner + "finite_signed_prime_identity"), H("finite signed prime identity"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("The exact original primeSymmetric action on the literal zero-extended complex head equals the full double coefficient sum. The actual floor(exp(L)) cutoff is reused, all diagonal and conjugated mixed terms remain, and no matrix identity is an input.")),
                        Paragraph(Text("For an integer c>=2 and L=log(c), the original PhysicalCompressedCosineMatrix.primeCutoff at half-window L/2 equals c: unfold primeCutoff, use Real.exp_log for positive c, and take the natural floor of c. Thus c=5040 and c=5041=71 squared give their exact inclusive cutoffs. PhysicalCompressedCosineMatrix.compression_zero_right and compression_zero_left make both shifts at +/-log(c) zero for every profile at the inclusive q=c row. At c=5041 the von Mangoldt weight of 71 squared remains nonzero; it is the compressed row that vanishes."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("prime-matrix-norm-le"),
                    DeclarationHandle.Create(Owner + "primeMatrix_norm_le"), H("primeMatrix norm le"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Actual integral entry bounds imply the bound 2*sum(abs(primeWeight(q))) at every finite cutoff."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("finite-signed-prime-norm-le"),
                    DeclarationHandle.Create(Owner + "finite_signed_prime_norm_le"), H("finite signed prime norm le"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The all-complex quadratic value is bounded by 2*sum(abs(primeWeight(q)))*(sum(norm(v_n))) squared, using actual integral estimates."))), DescribeRole.Theorem))));
}
