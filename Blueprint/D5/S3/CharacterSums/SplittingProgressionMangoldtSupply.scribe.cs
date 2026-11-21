using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class SplittingProgressionMangoldtSupplyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Simultaneous quadratic Mangoldt tests on a splitting progression",
        H("Exceptional indices for two character sums"),
        Blocks(
            Paragraph(Text("For x > 0, real y and t, and a natural cutoff N, write w(n) = Λ(n) min(1,x/n). "
                + "Let v be any real multiplier with |v(n)| ≤ 1. Assume every prime divisor p of the natural "
                + "stride m satisfies p ≤ y or N < p. Let P be the odd primes up to N coprime to m and set "
                + "a(p) = log(p) min(1,x/p) v(p). For a natural denominator d let F(d) be the full sum of "
                + "w(n)v(n)(n/d) for 1 ≤ n ≤ N and G(d) the sum of a(p)(p/d) over P.")),
            Describe.Lean(DescribeId.Create("discarded-mass"),
                DeclarationHandle.Create("D5/S3/CharacterSums/SplittingProgressionMangoldtSupply.clipped_coprime_prime_error"),
                H("Uniform discarded mass"), StatementSource.FromAuthor(F.Disp(Le(At("abs",F.Seq(At("F", F.Id("d")),
                    F.Minus,At("G", F.Id("d")))),F.Id("E")))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There exists an absolute K ≥ 0 such that E = K√x + log 2 + θ(y) "
                    + "works for every choice above and every d. The three terms bound higher prime powers, "
                    + "the prime 2, and the discarded odd prime divisors of m."))), DescribeRole.Theorem),
            Paragraph(Text("For the finite moment bound assume b ≡ 3 modulo 4 and 4 divides m. "
                + "Take arbitrary natural A and L, and write Fᵢ = F(b+m(A+i)) for 0 ≤ i < L. Let B be the sum "
                + "over all ordered p,r in P. Its diagonal summands are L a(p)². For p ≠ r, with h = L mod (pr), "
                + "the summand is |a(p)a(r)| min(h,pr−h). Write S = Σᵢ Fᵢ² and M = (√B + E√L)². Set H = Σᵢ max(0,|Fᵢ|−E)² and let J be the count "
                + "of i with t < |Fᵢ| multiplied by max(0,t−E)².")),
            Describe.Lean(DescribeId.Create("finite-clipped-progression"),
                DeclarationHandle.Create("D5/S3/CharacterSums/SplittingProgressionMangoldtSupply.finite_clipped_progression"),
                H("Finite moment and threshold bounds at any cutoff"), StatementSource.FromAuthor(
                    F.Disp(new Formula.Logic(Le(F.Id("S"),F.Id("M")), FormulaLogicOperator.And,
                        new Formula.Logic(Le(F.Id("H"),F.Id("B")), FormulaLogicOperator.And, Le(F.Id("J"), F.Id("B")))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An absolute K ≥ 0 works uniformly in all these parameters. "
                    + "The excess over E is at most the absolute retained prime sum. Expanding its square gives "
                    + "the diagonal bound L and the off-diagonal correlations. A full block of pr terms sums to zero. "
                    + "Removing full periods bounds the remainder by h, while completing the final block bounds "
                    + "it by pr−h. Cauchy–Schwarz gives the full second moment from the excess, and threshold counting gives the last inequality. Both also cover an empty interval."))),
                DescribeRole.Theorem),
            Paragraph(Text("Fix a real loss e > 0. At a real height x set u = x^(e/5), "
                + "N = floor(x^400) and t = x^(1/2+e)/2. For natural q,b,m,A,L take dᵢ = b + m(A+i) "
                + "for 0 ≤ i < L. Both sums run from n = 1 to N with coefficient Λ(n) min(1,x/n). "
                + "Their Jacobi factors are (n/dᵢ) and (n/q)(n/dᵢ), respectively. Mathlib defines (n/q) by multiplying over all prime factors of q with multiplicity, with empty product 1 at q = 0 or 1.")),
            Paragraph(Text("Write F(e,x,q,b,m,A,L) for the number of indices at which either sum has "
                + "absolute value strictly greater than t. In the formula, P(e,x,b,m,L) means that "
                + "b ≡ 3 modulo 4, that 4 divides m, that every prime divisor p of m satisfies p ≤ u "
                + "or N < p, and that exp(u/2) ≤ 2L.")),
            Describe.Lean(DescribeId.Create("splitting-progression-tests"),
                DeclarationHandle.Create("D5/S3/CharacterSums/SplittingProgressionMangoldtSupply.simultaneous_splitting_progression"),
                H("Uniform bound for failure of either test"),
                StatementSource.FromAuthor(Claim()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Expand the second moment for the retained odd primes coprime to m. "
                        + "The diagonal correlations are at most L. For distinct primes p,r the affine "
                        + "Jacobi correlation cancels on complete blocks of length pr, leaving an absolute "
                        + "error at most L mod pr. Taking absolute values of the cross terms permits the "
                        + "signed coefficients from the extra factor (n/q).")),
                    Paragraph(Text("The discarded higher prime powers contribute at most K√x. The prime "
                        + "2 costs at most log 2, and the discarded odd prime divisors of m cost at most "
                        + "the Chebyshev function θ(u). For x ≥ 1, both √x and u are at most x^(1/2+e/4). "
                        + "Thus the squared error per index is bounded by a constant times x·x^(e/2), uniformly in q and in the progression.")),
                    Paragraph(Text("For every sufficiently large x the length condition absorbs the "
                        + "remaining polynomial error in each second moment, giving a bound Lx·xᵉ "
                        + "for each sum of squares. An index failing either test contributes at least t² "
                        + "to their combined second moment. Dividing 2Lx·xᵉ by t² gives 8L/xᵉ. "
                        + "The indices represent integer candidates dᵢ. Selecting a prime dᵢ requires "
                        + "a prime-distribution estimate for the varying progression."))), DescribeRole.Theorem))));

    private static Formula Claim()
    {
        var e = F.Id("e");
        var x = F.Id("x");
        var threshold = F.Id("U");
        var names = new[] { "q", "b", "m", "A", "L" };
        var count = At("F", e, x, F.Id("q"), F.Id("b"), F.Id("m"), F.Id("A"), F.Id("L"));
        var size = F.Seq(F.Frac, F.Grp(F.D(8), F.Sp, F.Id("L")), F.Grp(x, F.Caret, F.Grp(e)));
        var allowed = At("P", e, x, F.Id("b"), F.Id("m"), F.Id("L"));
        Formula bound = Implies(allowed, Le(count, size));
        for (var i = names.Length - 1; i >= 0; i--)
            bound = Bind(FormulaQuantifier.ForAll, names[i], "N", bound);
        var late = Bind(FormulaQuantifier.ForAll, "x", "R", Implies(Le(threshold, x), bound));
        return F.Disp(Bind(FormulaQuantifier.Exists, "U", "R", late));
    }

    private static Formula At(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Bind(FormulaQuantifier kind, string variable, string domain, Formula body) =>
        new Formula.Bind(kind, FormulaIdentifier.Create(variable), F.Seq(F.Mathbb, F.Grp(F.Id(domain))), body);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
