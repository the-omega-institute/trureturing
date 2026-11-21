using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class SplittingProgressionMangoldtSupplyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Simultaneous quadratic Mangoldt tests on a splitting progression",
        H("Exceptional indices for two character sums"),
        Blocks(
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
