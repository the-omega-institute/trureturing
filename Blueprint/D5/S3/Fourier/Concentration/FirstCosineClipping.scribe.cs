using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class FirstCosineClippingDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/FirstCosineClipping";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first support change for two cosine constraints has an exact threshold and a quadratic rate in the modulus.",
        H("First clipping threshold for two cosine moments"),
        Blocks(
            Paragraph(Text(
                "For k modulo q write c(k) = cos(2πk/q), d(k) = cos(4πk/q), and s(k) = c(k)+d(k). "
                + "Let M₁ and M₂ denote the corresponding weighted moments, and let E be squared mass. "
                + "The threshold attached to an attained minimum m of s is T(m) = −1/(2m).")),
            Paragraph(Text(
                "For each real a ≥ 0, set v(k) = (1+2as(k))/q, L = (1+4a²)/q, "
                + "D(w) = E(w−v), and N(v) = Σₖ max(0,−v(k))². The notation P(w) "
                + "means w is a nonnegative real weight of total mass one with both moments at least a. "
                + "All competitors are real functions on the residues, and all k-sums run over the residues.")),
            Describe.Lean(
                DescribeId.Create("first-cosine-clipping"),
                DeclarationHandle.Create(Owner + ".first_cosine_clipping"),
                H("Sharp squared mass before clipping"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Character orthogonality gives the affine law total mass one and the two moments a. "
                        + "Expanding its squared distance from a mass-one competitor gives the exact remainder. "
                        + "Any feasible competitor pays at least the squared negative entries of that affine law. "
                        + "Equality with L forces all Euclidean distance terms to vanish.")),
                    Paragraph(Text(
                        "Completing the square gives s(k) = 2(c(k)+1/4)²−9/8. Twice c(k) is a sum of "
                        + "roots of unity and is integral over the integers. The rational value −1/2 would "
                        + "be a noninteger rational algebraic integer. This gives the strict lower bound on T(m). "
                        + "Rounding the angle whose cosine is −1/4 to the nearest grid point controls the "
                        + "squared error by (π/q)². The mean-zero and second-moment identities imply m ≤ −1/2 "
                        + "by summing (2−s(k))(s(k)−m). These two bounds control the reciprocal threshold."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var q = F.Id("q");
        var a = F.Id("a");
        var k = F.Id("k");
        var m = F.Id("m");
        var v = F.Id("v");
        var w = F.Id("w");
        var t = Call("T", m);
        var lower = F.Id("L");
        var reals = Seq(Mathbb, Grp(F.Id("R")));
        var domain = Seq(Mathbb, Grp(F.Id("Z")), Slash, q, Mathbb, Grp(F.Id("Z")), Sp, To, Sp, reals);
        var sum = new Formula.Subscript(Sum, k);
        var first = new Formula.Subscript(F.Id("M"), D(1));
        var second = new Formula.Subscript(F.Id("M"), D(2));
        Formula First(Formula x) => new Formula.Apply(first, [x]);
        Formula Second(Formula x) => new Formula.Apply(second, [x]);
        var fourNinths = Seq(Frac, Grp(D(4)), Grp(D(9)));
        var piSquared = new Formula.Power(Pi, D(2));
        return Disp(new Formula.Aligned([
            Seq(Amp, Forall, Sp, q, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")),
                Comma, Quad, Sp, q, Sp, Ge, Sp, D(5), Colon),
            Seq(Amp, Exists, Sp, m, Sp, InMacro, Sp, reals, Comma, Quad, Open,
                Exists, Sp, k, Comma, Sp, m, Eq, Call("s", k), Close,
                Sp, Land, Sp, Open, Forall, Sp, k, Comma, Sp, m, Sp, Le, Sp, Call("s", k), Close),
            Seq(Amp, Quad, Sp, Land, Sp, fourNinths, Lt, t, Sp, Le, Sp, fourNinths, Plus,
                Frac, Grp(D(1, 6), piSquared), Grp(D(9), new Formula.Power(q, D(2))), Comma),
            Seq(Amp, Quad, Sp, Forall, Sp, a, Sp, InMacro, Sp, reals, Comma, Quad, Sp,
                a, Sp, Ge, D(0), Colon),
            Seq(Amp, Quad, Sp, sum, Call("v", k), Eq, D(1), Comma, Quad, Sp,
                First(v), Eq, Second(v), Eq, a, Comma),
            Seq(Amp, Quad, Sp, Forall, Sp, w, Colon, domain, Comma, Quad, Sp,
                sum, Call("w", k), Eq, D(1), Sp, Longrightarrow, Sp,
                Call("E", w), Minus, lower, Eq, Call("D", w), Plus,
                Frac, Grp(D(4), a), Grp(q), Open, First(w), Plus, Second(w), Minus, D(2), a, Close, Comma),
            Seq(Amp, Quad, Sp, Forall, Sp, w, Colon, domain, Comma, Quad, Sp,
                Call("P", w), Sp, Longrightarrow, Sp, lower, Plus, Call("N", v), Sp, Le, Sp,
                Call("E", w), Sp, Land, Sp, Open, Call("E", w), Eq, lower, Sp, Iff, Sp, w, Eq, v, Close, Comma),
            Seq(Amp, Quad, Sp, Open, Exists, Sp, w, Colon, domain, Comma, Sp,
                Call("P", w), Sp, Land, Sp, Call("E", w), Eq, lower, Close,
                Sp, Iff, Sp, a, Sp, Le, Sp, t, Dot)
        ]));
    }
}
