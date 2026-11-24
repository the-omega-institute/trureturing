using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class SixResidueMomentOptimumDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/SixResidueMomentOptimum";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two real character modes on six residues have an exact common-threshold minimum squared mass.",
        H("Minimum squared mass for two modes modulo six"),
        Blocks(
            Paragraph(Text(
                "Use the residues k = 0 through 5 and the real modes c(k) = cos(πk/3) and "
                + "d(k) = cos(2πk/3). Write E for the sum of squared weights and M₁, M₂ for "
                + "the respective weighted moments, with each sum over the six residues. "
                + "For a ≤ 1/2 take v = ((1+4a)/6, 1/6, (1−2a)/6, 1/6, (1−2a)/6, 1/6). "
                + "For a > 1/2 take v = (a, (1−a)/3, 0, (1−a)/3, 0, (1−a)/3). "
+ "For every real t, put uₜ(k) = max(0, 1 − t(1−c(k))) and "
+ "pₜ(k) = uₜ(k)/∑ⱼuₜ(j). For a competitor w write D(w) = E(w) − E(v) − E(w−v) "
                + "and m(w) = M₁(w) + M₂(w) − 2a.")),
            Describe.Lean(
                DescribeId.Create("six-residue-two-mode-optimum"),
                DeclarationHandle.Create(Owner + ".six_two_mode_optimum"),
                H("The common-threshold optimum and the one-mode comparison"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The energy comparison applies to every nonnegative probability law "
                        + "w for which M₁(w) + M₂(w) ≥ 2a. This includes arbitrary nonsymmetric "
                        + "laws satisfying the two individual bounds. The exact energy identity needs "
                        + "only total mass one. In the upper regime the last term retains the "
                        + "contribution of the two clipped residues 2 and 4.")),
                    Paragraph(Text(
                        "The combined readout c+d takes the values 2, 0 and −1. On each set "
                        + "where c+d is constant the differences c−d sum to zero. A weight "
                        + "depending only on c+d therefore has equal moments M₁ and M₂. "
                        + "Apply the one-moment optimizer to c+d at threshold 2a and anchor 2. "
                        + "The cutoff is 1/2. The indices with aggregate readout −1 vanish "
                        + "when t reaches 1/3, corresponding to a = 1/2. Evaluating the "
                        + "remaining affine weights yields the two formulas.")),
                    Paragraph(Text(
                        "For the optimizer of the first mode alone, attaining an interior "
                        + "moment requires 0 < t < 2. Its raw weight at residue 1 then "
                        + "exceeds its raw weight at residue 3, and residues 1 and 5 have "
                        + "equal weight. Since M₁(p)−M₂(p) = p(1)+p(5)−2p(3), this gives "
                        + "the strict comparison."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var a = F.Id("a");
        var k = F.Id("k");
        var v = F.Id("v");
        var w = F.Id("w");
        var t = F.Id("t");
        var p = new Formula.Subscript(F.Id("p"), t);
        var reals = Seq(Mathbb, Grp(F.Id("R")));
        var domain = Seq(Call("Fin", D(6)), Sp, To, Sp, reals);
        var sum = new Formula.Subscript(Sum, k);
        var first = new Formula.Subscript(F.Id("M"), D(1));
        var second = new Formula.Subscript(F.Id("M"), D(2));
        var half = Seq(Frac, Grp(D(1)), Grp(D(2)));
        var ev = Call("E", v);
        var aSquared = new Formula.Power(a, D(2));
        return Disp(new Formula.Aligned([
            Seq(Amp, Forall, Sp, a, Sp, InMacro, Sp, reals, Comma, Quad,
                D(0), Sp, Le, Sp, a, Sp, Le, Sp, D(1), Colon),
            Seq(Amp, Forall, Sp, k, Comma, Sp, Call("v", k), Sp, Ge, D(0), Comma,
                Quad, Sp, sum, Call("v", k), Eq, D(1), Comma, Quad, Sp,
                new Formula.Apply(first, [v]), Eq, new Formula.Apply(second, [v]), Eq, a, Comma),
            Seq(Amp, a, Sp, Le, Sp, half, Sp, Longrightarrow, Sp, ev, Eq, Frac,
                Grp(D(1), Plus, D(4), aSquared), Grp(D(6)), Comma),
            Seq(Amp, half, Lt, a, Sp, Longrightarrow, Sp, ev, Eq, aSquared, Plus,
                Frac, Grp(new Formula.Power(Seq(Open, D(1), Minus, a, Close), D(2))), Grp(D(3)), Comma),
            Seq(Amp, Forall, Sp, w, Colon, domain, Comma, Quad,
                sum, Call("w", k), Eq, D(1), Colon),
            Seq(Amp, Quad, a, Sp, Le, Sp, half, Sp, Longrightarrow, Sp, Call("D", w), Eq,
                Frac, Grp(D(2), a), Grp(D(3)), Call("m", w), Comma),
            Seq(Amp, Quad, half, Lt, a, Sp, Longrightarrow, Sp, Call("D", w), Eq,
                Frac, Grp(D(4), a, Minus, D(1)), Grp(D(3)), Call("m", w), Plus,
                Open, D(2), a, Minus, D(1), Close,
                Open, Call("w", D(2)), Plus, Call("w", D(4)), Close, Comma),
            Seq(Amp, Forall, Sp, w, Colon, domain, Comma, Quad, Open, Forall, Sp, k, Comma, Sp,
                Call("w", k), Sp, Ge, D(0), Close, Sp, Land, Sp, sum, Call("w", k), Eq, D(1), Sp,
                Land, Sp, new Formula.Apply(first, [w]), Plus, new Formula.Apply(second, [w]),
                Sp, Ge, Sp, D(2), a),
            Seq(Amp, Quad, Sp, Longrightarrow, Sp, Call("E", Seq(w, Minus, v)), Sp, Le, Sp,
                Call("E", w), Minus, ev, Comma),
            Seq(Amp, Forall, Sp, t, Sp, InMacro, Sp, reals, Comma, Quad, D(0), Lt, a, Lt, D(1),
                Sp, Land, Sp, new Formula.Apply(first, [p]), Eq, a, Sp, Longrightarrow, Sp,
                new Formula.Apply(second, [p]), Lt, a, Dot)
        ]));
    }
}
