using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class SigmaNeighbourPeakDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/SigmaNeighbourPeak.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Primorial divisor sums dominate both adjacent divisor sums by any prescribed factor.",
        H("Arbitrarily high simultaneous sigma peaks"),
        Blocks(
            Describe.Lean(DescribeId.Create("a397578-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("The exact OEIS conjecture"),
                StatementSource.FromAuthor(ClaimFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Ratushnyak's OEIS A397578 defines a(n) as the least k for which "
                    + "sigma(k) exceeds n times each of sigma(k-1) and sigma(k+1). "
                    + "Here sigma means the sum of positive divisors, sigma(1,k) in Lean. "
                    + "The claim includes all natural n, requires k >= 2, and uses strict "
                    + "inequalities on both sides. Natural subtraction is truncated, but "
                    + "the lower bound on k makes k-1 positive. Existence implies the "
                    + "least such k exists by well-ordering."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a397578-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Every factor is attained"),
                StatementSource.FromAuthor(ClaimFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Set P = primorial(x), the product of primes at most x, with x >= 4. "
                    + "The existing reciprocal_divisor_sum identity identifies sigma(P)/P "
                    + "with the sum of reciprocal divisors. Each prime at most x is a divisor; "
                    + "divergence of the prime reciprocal series therefore gives an x with "
                    + "sigma(P) > 6nP. Neither P-1 nor P+1 has a prime factor at most x. "
                    + "For either neighbour m, the product of its distinct prime factors "
                    + "divides m, so 4^omega(m) <= m <= 4^x+1 < 4^(x+1), giving "
                    + "omega(m) <= x. The finite prime-power geometric sums give "
                    + "sigma(m)/m <= product over p dividing m of p/(p-1). Each factor "
                    + "is at most 1+1/x. Consequently sigma(m)/m <= (1+1/x)^x <= e < 3. "
                    + "Combining these estimates proves both inequalities, including n=0. "
                    + "This is an unbounded existence proof with a primorial witness; "
                    + "it does not bound the least witness's growth or characterize it as "
                    + "highly abundant."))),
                DescribeRole.Theorem, new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a397578-sigma-neighbour-peaks"),
                    ResolutionKind.Proved)))));

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var sigma = Call("sigma", D(1), k);
        return Disp(Seq(Forall, Sp, n, Colon, Sp, Naturals(), Comma, Sp,
            Exists, Sp, k, Colon, Sp, Naturals(), Comma, Sp,
            And(Le(D(2), k), And(
                Lt(Mul(n, Call("sigma", D(1), Sub(k, D(1)))), sigma),
                Lt(Mul(n, Call("sigma", D(1), Add(k, D(1)))), sigma)))));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
}
