using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class FiniteFrobeniusDiscriminantSignDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Factorization/QuadraticIdeals/FiniteFrobeniusDiscriminantSign.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact finite-matrix distribution of the discriminant sign at fixed determinant.",
        H("Finite matrix discriminant sign law"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-discriminant-shifted-character-sum"),
                DeclarationHandle.Create(Module + "sum_character_shifted_square"),
                H("Shifted square character sum is minus one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An explicit hyperbola factorization counts all square roots over the entire field "
                    + "by bijection with nonzero field elements."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-discriminant-zero-card"),
                DeclarationHandle.Create(Module + "discriminant_zero_card"),
                H("Exact zero-discriminant trace count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The cardinality of the trace values with zero discriminant is one plus the "
                    + "determinant quadratic character."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-discriminant-sign-moments"),
                DeclarationHandle.Create(Module + "discriminant_sign_moments"),
                H("Exact matrix-weighted sign moments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The first and second moments use the true matrix trace fiber size at fixed "
                    + "determinant, not a uniform distribution on trace values."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-discriminant-fair-nonsquare"),
                DeclarationHandle.Create(Module + "nonsquare_det_sign_fair"),
                H("A nonsquare determinant yields an exactly fair sign bit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The positive and negative sign masses are each one half and no zero discriminants "
                    + "occur. This is a finite input for arithmetic independence tests, not a density "
                    + "theorem."))),
                DescribeRole.Theorem))));
}
