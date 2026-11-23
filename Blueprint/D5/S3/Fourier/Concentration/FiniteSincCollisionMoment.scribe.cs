using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class FiniteSincCollisionMomentDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/FiniteSincCollisionMoment";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted near-collisions control finite-time moments and bound the start of a missing window.",
        H("Finite Tail Moments from Weighted Near-Collisions"),
        Blocks(
            Paragraph(Text(
                "For a finite index type J, write Z(t) for the weighted sum of exp(i g(j)t). "
                + "A degree-p count vector m has frequency G(m) equal to the sum of m(j)g(j), "
                + "and coefficient c(m) equal to the multinomial coefficient times the product "
                + "of w(j) to the power m(j). E(p,r) is the ordered sum of c(m)c(n) over "
                + "degree-p pairs with absolute frequency difference at most r. "
                + "M(p,L,s) averages the 2p-th power of the norm of Z(s+u+t) over two "
                + "independent uniform offsets u and t in the closed interval from -L/2 to L/2.")),
            Describe.Lean(
                DescribeId.Create("tail-moment-comparison"),
                DeclarationHandle.Create(Owner + ".tail_moment_comparison"),
                H("The averaging radius determines the near-collision scale"),
                StatementSource.FromAuthor(Comparison()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The power expansion reduces the moment to an ordered pair sum. "
                    + "Each pair contributes a squared sinc at its scaled frequency difference. "
                    + "At center zero each term is nonnegative, and pairs within distance 2/L "
                    + "retain at least one quarter of their weight. For the upper bound, "
                    + "group frequencies into bins of width 2/L. The reciprocal-square "
                    + "bound gives each row of the bin majorant total at most seven. "
                    + "The inequality 2uv ≤ u²+v² bounds the resulting quadratic form by "
                    + "seven times the sum of squared bin masses. Each same-bin pair lies "
                    + "within the collision radius, even if some frequencies coincide."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bounded-tail-window"),
                DeclarationHandle.Create(Owner + ".exists_bounded_tail_window"),
                H("The near-collision budget confines the window start"),
                StatementSource.FromAuthor(Window()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Average the sum of the grid moments over candidate starts centered "
                        + "at A+L. The weighted bound is uniform in the center, including every "
                        + "grid offset. If each start in the open interval had a bad grid node, "
                        + "the averaged sum would be at least the power of the threshold. "
                        + "The strict budget therefore gives a common good start in that interval. "
                        + "The imaginary part gives the signed bound at grid nodes. The mesh "
                        + "amends it by at most hB throughout the closed window, including its "
                        + "right endpoint.")),
                    Paragraph(Text(
                        "This result gives a finite search interval when an estimate of the "
                        + "weighted collision mass is supplied at the corresponding resolution. "
                        + "It applies to repeated frequencies. For a tail of actual zeta "
                        + "ordinates at moment order growing with the cutoff, the necessary "
                        + "arithmetic estimate remains open.")),
                    Paragraph(Ref("D5/S3/Fourier/Concentration/FiniteTailMomentMissingWindow"))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula TailParameters() => Seq(
        Forall, Sp, F.Id("J"), Colon, Sp, Operatorname, Grp(F.Id("FiniteType")), Comma, Quad, Sp,
        F.Id("g"), Comma, F.Id("w"), Colon, Sp, F.Id("J"), To, Reals, Comma, Quad, Sp,
        F.Id("p"), Colon, Sp, Mathbb, Grp(F.Id("N")), Comma);

    private static Formula NonnegativeWeights() => Seq(
        Open, Forall, Sp, F.Id("j"), Sp, InMacro, Sp, F.Id("J"), Comma, Sp,
        Call("w", F.Id("j")), Ge, D(0), Close);

    private static Formula Collision(Formula radius) => Call("E", F.Id("p"), radius);

    private static Formula Comparison()
    {
        var length = F.Id("L");
        var center = F.Id("s");
        var collision = Collision(new Formula.Fraction(D(2), length));
        return Disp(new Formula.Aligned([
            TailParameters(),
            Seq(length, Comma, center, Colon, Sp, Reals, Comma),
            Seq(NonnegativeWeights(), Quad, Sp, Land, Sp, length, Gt, D(0), Quad, Sp, Longrightarrow),
            Seq(new Formula.Fraction(collision, D(4)), Le, Call("M", F.Id("p"), length, D(0)),
                Quad, Sp, Land, Quad, Sp, Call("M", F.Id("p"), length, center),
                Le, Multiply(D(7), collision)),
        ]));
    }

    private static Formula Window()
    {
        var a = F.Id("A");
        var b = F.Id("b");
        var h = F.Id("h");
        var horizon = F.Id("H");
        var length = F.Id("L");
        var t = F.Id("t");
        var j = F.Id("j");
        var w = Call("w", j);
        var g = Call("g", j);
        var slope = Seq(Sum, Underscore, Grp(j, Sp, InMacro, Sp, F.Id("J")), Sp,
            Multiply(w, new Formula.Absolute(g)));
        var score = Seq(Sum, Underscore, Grp(j, Sp, InMacro, Sp, F.Id("J")), Sp,
            Multiply(w, Call("sin", Multiply(g, t))));
        var floor = Seq(new Formula.Floor(new Formula.Fraction(horizon, h)), Underscore, Grp(Plus));
        var window = Seq(OpenBracket, b, Comma, Add(b, horizon), CloseBracket);
        var budget = Multiply(Multiply(D(7), Seq(Open, Add(floor, D(1)), Close)),
            Collision(new Formula.Fraction(D(2), length)));
        return Disp(new Formula.Aligned([
            TailParameters(),
            Seq(length, Comma, horizon, Comma, h, Comma, DeltaLower, Comma, a, Colon, Sp, Reals, Comma),
            Seq(NonnegativeWeights(), Quad, Sp, Land, Sp, length, Gt, D(0),
                Quad, Sp, Land, Sp, h, Gt, D(0), Quad, Sp, Land, Sp, DeltaLower, Ge, D(0), Quad, Sp, Land),
            Seq(budget, Lt, new Formula.Power(DeltaLower, Multiply(D(2), F.Id("p"))),
                Quad, Sp, Longrightarrow),
            Seq(Exists, Sp, b, Colon, Sp, Reals, Comma, Sp, a, Lt, b, Lt, Add(a, Multiply(D(2), length)),
                Quad, Sp, Land, Sp, Forall, Sp, t, Sp, InMacro, Sp, window, Comma),
            Seq(score, Lt, Add(DeltaLower, Multiply(h, Seq(Open, slope, Close)))),
        ]));
    }
}
