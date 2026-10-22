using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class OriginalSignedPrimeArithmeticDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaBridge/OriginalSignedPrimeArithmetic.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Variable arithmetic certificates identify prime-power weights and bound their two logarithmic coefficients. The original full-complex estimate supplies the row, uniqueness, rational-ceiling and complete support premises.",
        H("OriginalSignedPrimeArithmetic"),
        Blocks(
                Paragraph(Text("Variable arithmetic certificates identify prime-power weights and bound their two logarithmic coefficients. The original full-complex estimate supplies the row, uniqueness, rational-ceiling and complete support premises.")),
                Paragraph(Text("ArithmeticCertificate requires q>=2, q<5040, positive a, a<=b, prime p, positive k, and q=p^k for every supplied row. It also requires distinct q values, both rational log-ceiling inequalities, and the equivalence primeFactors.card=1 iff membership in the supplied support for every n:Fin 5041. This quantifies over missing integers as well as all 717 present rows.")),
                Paragraph(Text("weight_row rewrites the existing primeWeight definition with ArithmeticFunction.vonMangoldt_apply_pow and vonMangoldt_apply_prime. weight_zero_of_missing uses the upstream prime-power characterization and vonMangoldt_eq_zero_iff. No original positive weight is replaced with a fabricated signed or truncated weight.")),
                Paragraph(Text("The rational logUpper uses p.log2 and the repository mathlib bound Real.log_two_lt_d9. log_le_upper applies log(x)<=x-1 after division by 2^p.log2, then bounds the log(2) term. row_log_bounds combines this analytic argument with the supplied exact rational ceilings. The exact rational ceiling checks are supplied by original_prime80.")),
                Describe.Lean(DescribeId.Create("ArithmeticCertificate"),
                    DeclarationHandle.Create(Owner + "ArithmeticCertificate"), H("ArithmeticCertificate"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The exact row, support, uniqueness and rational-ceiling premises for a variable arithmetic table."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("row-of-mem"),
                    DeclarationHandle.Create(Owner + "row_of_mem"), H("row of mem"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Every member row satisfies the full certified row-validity conjunction."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("weight-row"),
                    DeclarationHandle.Create(Owner + "weight_row"), H("weight row"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The density interpretation uses the existing prime-power and prime von Mangoldt identities on certified row data."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("weight-zero-of-missing"),
                    DeclarationHandle.Create(Owner + "weight_zero_of_missing"), H("weight zero of missing"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Complete support over Fin 5041 and the upstream von Mangoldt zero criterion remove missing arithmetic indices."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("row-log-bounds"),
                    DeclarationHandle.Create(Owner + "row_log_bounds"), H("row log bounds"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("A real log bound and exact rational ceilings give both coefficients needed for the two signed cosh identities."))), DescribeRole.Theorem))));
}
