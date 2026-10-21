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
                    Blocks(Paragraph(Text("The exact original primeSymmetric action on the literal zero-extended complex head equals the full double coefficient sum. The actual floor(exp(L)) cutoff is reused, all diagonal and conjugated mixed terms remain, and no matrix identity is an input."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("prime-matrix-hermitian"),
                    DeclarationHandle.Create(Owner + "primeMatrix_hermitian"), H("primeMatrix hermitian"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Adjointness of opposite physical shifts implies Hermiticity of the actual signed finite matrix."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("finite-signed-prime-real"),
                    DeclarationHandle.Create(Owner + "finite_signed_prime_real"), H("finite signed prime real"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Conjugation and exchanging the two finite indices prove reality of the full complex quadratic form. No real-coefficient restriction or positivity conclusion is made."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("prime-matrix-norm-le"),
                    DeclarationHandle.Create(Owner + "primeMatrix_norm_le"), H("primeMatrix norm le"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Actual integral entry bounds imply the bound 2*sum(abs(primeWeight(q))) at every finite cutoff."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("finite-signed-prime-norm-le"),
                    DeclarationHandle.Create(Owner + "finite_signed_prime_norm_le"), H("finite signed prime norm le"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The all-complex quadratic value is bounded by 2*sum(abs(primeWeight(q)))*(sum(norm(v_n))) squared, using actual integral estimates."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("logarithmic-cutoff"),
                    DeclarationHandle.Create(Owner + "logarithmic_cutoff"), H("logarithmic cutoff"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("For every integer c>=2 the half-window log(c)/2 has exact inclusive cutoff c. Both compressed shifts at log(c) vanish for every profile even when their prime-power weight is nonzero."))), DescribeRole.Theorem))));
}
