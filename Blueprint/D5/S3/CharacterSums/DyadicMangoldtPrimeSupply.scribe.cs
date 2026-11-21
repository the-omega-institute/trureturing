using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class DyadicMangoldtPrimeSupplyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Square-root cancellation for auxiliary primes on arbitrarily high dyadic scales",
        H("The quadratic Mangoldt sum on dyadic prime bands"),
        Blocks(
            Paragraph(Text("Fix ε > 0. In block k put X = 2ᵏ, x = (k log 2)^(5/ε) and N = floor(x^400). "
                + "For primes q congruent to 3 modulo 8 in [X/2,X), form the real sum from n = 1 to N "
                + "of Λ(n) min(1,x/n) times the Jacobi symbol (n/q). "
                + "B(ε,k) and G(ε,k) sum (log q)/q over primes whose absolute sum respectively exceeds "
                + "or is at most x^(1/2+ε)/2. At k = 0 the implementation uses [1,2), of zero weight. In the formula, summableBad(e) means that the block weights B(e,k) have a convergent series, and accepted(e,K) sums G(e,k) from k = 1 through K.")),
            Describe.Lean(DescribeId.Create("dyadic-mangoldt-supply"),
                DeclarationHandle.Create("D5/S3/CharacterSums/DyadicMangoldtPrimeSupply.dyadic_quadratic_mangoldt_supply"),
                H("Finite exceptional weight and divergent accepted weight"),
                StatementSource.FromAuthor(Claim()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Represent the clipping factor by integrating x/t² for t greater "
                        + "than both x and n. The nonprime contribution is controlled by the Chebyshev bound "
                        + "ψ(t) − θ(t) ≤ C√t. Integration costs at most 2C√x, uniformly in the cutoff N.")),
                    Paragraph(Text("For the remaining odd prime terms expand the square and average over "
                        + "all integers congruent to 3 modulo 8 in the band. Distinct primes p,r have zero "
                        + "complete correlation and an incomplete-period error at most 8pr. The diagonal "
                        + "costs at most the band length times the sum of the squared coefficients. "
                        + "The harmonic bound controls this sum by x(log N)²(1+log N).")),
                    Paragraph(Text("The band length grows exponentially in x^(ε/5). It absorbs the "
                        + "polynomial endpoint error. Restrict to prime denominators by positivity and "
                        + "bound exceptions using the square of the threshold. Eventually the bad "
                        + "weight per block is at most 4/((log 2)⁴ k⁴). The complete residue class has "
                        + "divergent logarithmic prime weight. Subtract the finite exceptional total "
                        + "and telescope the disjoint blocks.")),
                    Paragraph(Text("This supplies arbitrarily high dyadic scales. In the modulus-one "
                        + "comparison the approximation by the logarithmic derivative, its zero "
                        + "exclusions, and the choice of the second prime require further estimates."))),
                DescribeRole.Theorem))));

    private static Formula Claim()
    {
        var e = F.Id("e");
        var k = F.Id("K");
        var m = F.Id("M");
        var s = F.Id("S");
        var partial = At("accepted", e, k);
        var late = All("M", "R", Exists("S", "N", All("K", "N",
            Implies(Le(s, k), Le(m, partial)))));
        var finite = At("summableBad", e);
        return F.Disp(All("e", "R", Implies(new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, e),
            new Formula.Logic(finite, FormulaLogicOperator.And, late))));
    }

    private static Formula At(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string name, string domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Space(domain), body);
    private static Formula Exists(string name, string domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), Space(domain), body);
    private static Formula Space(string name) => F.Seq(F.Mathbb, F.Grp(F.Id(name)));
}
