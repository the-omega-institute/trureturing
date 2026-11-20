using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class GoldenCubicFormalConjugacyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Formal rational power series conjugate Lucas polynomials to a scaling, without choosing a square root.",
        H("Root-free formal conjugacy for Chebyshev multipliers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("native-rootfree-cubic-formal-conjugacy"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/GoldenCubicFormalConjugacy.formal_conjugacy"),
                H("Cubic formal conjugacy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the series with coefficient two divided by the factorial of twice its index and zero constant coefficient, the cubic update in shifted coordinates is exactly rescaling its argument by nine."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-rootfree-chebyshev-formal-conjugacy"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/GoldenCubicFormalConjugacy.chebyshev_formal_conjugacy"),
                H("Every natural Chebyshev multiplier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Injectivity of the formal substitution that doubles the degree and the formal exponential product identity give scaling by the square of every natural multiplier. This statement is over rational formal power series; it does not assert p-adic convergence, evaluated conjugacy, or an analytic inverse."))),
                DescribeRole.Theorem))));
}
