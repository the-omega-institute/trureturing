using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class GoldenCubicFactorRoleDigitsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Arith/Primes/GoldenCubicFactorRoleDigits";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A square-times-cube native Lucas block forces different congruences on its two factor roles.",
        H("Exact digits of native cubic Lucas factor roles"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-cubic-factor-role-square-digit"),
                DeclarationHandle.Create(Module + ".native_square_role_digits"),
                H("The square-role first ternary digit alternates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The native Fibonacci rank controls the denominators of both prime factors. "
                    + "The block's first nonzero ternary digit comes entirely from the square role."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-factor-role-valuation"),
                DeclarationHandle.Create(Module + ".square_role_pred_valuation"),
                H("The square-role prime predecessor has exact ternary depth"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The prime minus one is divisible by the next ternary power, but not the following one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-factor-role-dyadic-coupling"),
                DeclarationHandle.Create(Module + ".cube_role_mod128_coupling"),
                H("The cube-role dyadic residue is tied to the square role"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Modulo 128 the cube-role factor is 43 times the tenth power of the square-role factor. "
                    + "In particular it is always 3 modulo 8, and its native prime-rank condition supplies 19 modulo 24."))),
                DescribeRole.Theorem))));
}
