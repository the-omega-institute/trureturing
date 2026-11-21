using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class SplittingProgressionExponentialTailDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Power saving for the two quadratic tests",
        H("Exponential decay of the exceptional fraction"),
        Blocks(
            Paragraph(Text("Fix ε > 0 and a real number B. At a real height x set y = x^(ε/5), "
                + "N = floor(x^400) and D = exp(y (log x)²). For 0 ≤ i < L let dᵢ = b + m(A+i). "
                + "Both tests sum Λ(n) min(1,x/n) over 1 ≤ n ≤ N, weighted by J(n,dᵢ) "
                + "and by J(n,q)J(n,dᵢ), respectively. The Jacobi symbol uses Mathlib's product "
                + "over prime factors with multiplicity, including its value 1 for q = 0 or 1.")),
            Paragraph(Text("Write F(ε,x,q,b,m,A,L) for the number of indices where at least one "
                + "absolute value exceeds x^(1/2+ε)/2. In the display e denotes ε. The predicate "
                + "P(e,x,b,m,L) requires b ≡ 3 modulo 4, 4 dividing m, every prime divisor p of m "
                + "satisfying p ≤ y or N < p, and D/(4 exp(4y)) ≤ L.")),
            Describe.Lean(DescribeId.Create("splitting-exponential-tail"),
                DeclarationHandle.Create("D5/S3/CharacterSums/SplittingProgressionExponentialTail.splitting_progression_exponential_tail"),
                H("Uniform exponential bound for failure of either test"),
                StatementSource.FromAuthor(Claim()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Removing higher prime powers and prime divisors of m costs at most "
                        + "K√x + log 2 + θ(x^(1/2+ε/2)). At every sufficiently large height this is at most a quarter "
                        + "of x^(1/2+ε), uniformly for either twist.")),
                    Paragraph(Text("Use the even moment 2k with k = floor(y log(x)/4800). By the Chinese remainder theorem "
                        + "the complete affine progression has independent residue coordinates. Each signed "
                        + "quadratic coordinate has mean zero and takes the values −1, 0, 1. For real weights "
                        + "aₚ its exponential average is bounded by exp(t²aₚ²/2), giving a complete mean "
                        + "moment at most 2(2 exp(1) k V)^k for V bounding the sum of the squared weights.")),
                    Paragraph(Text("Expand both moments over the same tuples of primes. Each tuple contributes "
                        + "an endpoint error bounded by twice the product of its primes, allowing repetitions. "
                        + "Summing the absolute weighted errors costs at most 2(Σ p|aₚ|)^(2k). This is bounded by 2 exp(2400k log x), "
                        + "while the prescribed interval length grows on the scale exp(y(log x)²−O(y)). "
                        + "Counting indices above the remaining threshold and adding the two counts gives the bound. "
                        + "Selection of a prime denominator also requires enough primes in that progression."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("splitting-power-tail"),
                DeclarationHandle.Create("D5/S3/CharacterSums/SplittingProgressionExponentialTail.splitting_progression_power_tail"),
                H("Power saving on the length scale D"),
                StatementSource.FromAuthor(Claim(powerSaving: true)), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix ε > 0. In the display c denotes min(ε,1)/38400 and R has the same "
                        + "conditions as P with the allowed small-prime cap raised to x^(1/2+ε/2). "
                        + "With k as above, the complete moment gains a factor exponential in −k log x. "
                        + "The interval endpoint error is at most 2 exp(y(log x)²/2). "
                        + "Division by L and the test threshold gives the displayed bound. "
                        + "Since c(log x)² exceeds any fixed B eventually, this also gives the fixed-rate theorem."))), DescribeRole.Theorem))));

    private static Formula Claim(bool powerSaving = false)
    {
        var e = F.Id("e");
        var x = F.Id("x");
        var threshold = F.Id("U");
        var names = new[] { "q", "b", "m", "A", "L" };
        var count = At("F", e, x, F.Id("q"), F.Id("b"), F.Id("m"), F.Id("A"), F.Id("L"));
        var y = F.Seq(x, F.Caret, F.Grp(F.Frac, F.Grp(e), F.Grp(F.D(5))));
        var exponent = powerSaving
            ? F.Seq(F.Minus, F.Id("c"), F.Sp, y, F.Sp, F.Grp(At("log", x)), F.Caret, F.Grp(F.D(2)))
            : F.Seq(F.Minus, F.Id("B"), F.Sp, y);
        var size = F.Seq(F.Id("L"), F.Sp, At("exp", exponent));
        var allowed = At(powerSaving ? "R" : "P", e, x, F.Id("b"), F.Id("m"), F.Id("L"));
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
