using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class ClippedMomentWeightsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/ClippedMomentWeights";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A normalized positive part minimizes squared mass with a lower bound on one real moment.",
        H("Minimum squared mass with one lower moment bound"),
        Blocks(Paragraph(Text(
            "For a finite index set I and real values cᵢ, let C be any attained value and a ≤ C. "
            + "Write μ for the uniform mean, M for the real moment and E for the squared mass.")),
        Describe.Lean(
            DescribeId.Create("clipped-moment-minimizer"),
            DeclarationHandle.Create(Owner + ".exists_clipped_moment_minimizer"),
            H("Exact optimizer for one real lower moment bound"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Fourier/zhouliu2025simplexprojection")),
            Blocks(
                Paragraph(Text(
                    "Let I be a finite set, let c be a real readout on I, and take a target a "
                    + "at most an attained value C. Write μ for the uniform mean of c, "
                    + "M(w) for the weighted moment, E(w) for the sum of squared weights, "
                    + "and Z for the sum of the raw clipped weights u. All sums range over I. The identity "
                    + "holds for any real w of sum one. The inequality applies when w is "
                    + "also nonnegative and M(w) is at least a.")),
                Paragraph(Text(
                    "Zhou and Liu study Euclidean projection onto the intersection of the "
                    + "simplex and one linear half-space. With center zero and half-space "
                    + "vector −c, their shifted simplex projection gives the thresholded "
                    + "affine form for this objective.")),
                Paragraph(Text(
                    "At t = 0 the weights are uniform. Every index attaining C has raw "
                    + "weight one for all t, so the denominator stays positive. At the largest "
                    + "reciprocal of a positive gap C − cᵢ, or zero if there are no such gaps, all weights below C have "
                    + "vanished. The normalized moment is then at least C. Continuity gives "
                    + "a finite parameter for the required moment.")),
                Paragraph(Text(
                    "The affine constant disappears in the inner product with w − v by "
                    + "equality of total mass. At each clipped entry v vanishes, so replacing "
                    + "the negative raw weight by zero adds the clipped contribution in the "
                    + "identity. Both terms of the correction are nonnegative for feasible "
                    + "w when the moment bound is active. At t = 0 the correction is zero. "
                    + "The squared distance forces uniqueness.")),
                Paragraph(Text(
                    "On a finite cyclic group the readout can be the real part of a character "
                    + "at a single spatial residue. A whole spatial band imposes further "
                    + "joint constraints."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var i = F.Id("i");
        var j = F.Id("j");
        var c = new Formula.Subscript(F.Id("c"), i);
        var v = new Formula.Subscript(F.Id("v"), i);
        var w = new Formula.Subscript(F.Id("w"), i);
        var u = new Formula.Subscript(F.Id("u"), i);
        var uj = new Formula.Subscript(F.Id("u"), j);
        var a = F.Id("a");
        var cap = F.Id("C");
        var t = F.Id("t");
        var sum = new Formula.Subscript(Sum, i);
        var mean = Mu;
        var z = F.Id("Z");
        var upper = F.Id("T");
        var readout = F.Id("w");
        var energyDistance = Seq(sum, new Formula.Power(Seq(Open, w, Minus, v, Close), D(2)));
        var gap = Seq(Call("E", F.Id("w")), Minus, Call("E", F.Id("v")));
        var momentGap = Seq(Call("M", F.Id("w")), Minus, Call("M", F.Id("v")));
        var offset = Seq(t, Open, cap, Minus, c, Close, Minus, D(1));
        var positive = new Formula.Subscript(Seq(Open, offset, Close), Plus);
        return Disp(new Formula.Aligned([
            Seq(Amp, upper, Eq, Max, Open, OpenBrace, D(0), CloseBrace, Sp, Cup, Sp, OpenBrace,
                Frac, Grp(D(1)), Grp(cap, Minus, c), Sp, Mid, Sp, c, Lt, cap, CloseBrace, Close, Comma),
            Seq(Amp, Exists, Sp, t, Sp, InMacro, Sp, OpenBracket, D(0), Comma, upper, CloseBracket,
                Comma, Quad, Sp, a, Sp, Le, Sp, mean, Sp, Longrightarrow, Sp, t, Eq, D(0), Comma),
            Seq(Amp, u, Eq, Max, Open, D(0), Comma, D(1), Minus, t, Open, cap, Minus, c, Close, Close,
                Comma, Quad, Sp, v, Eq, Frac, Grp(u), Grp(z), Comma,
                Quad, Sp, z, Eq, new Formula.Subscript(Sum, j), uj, Comma),
            Seq(Amp, v, Sp, Ge, D(0), Comma, Quad, Sp, sum, v, Eq, D(1), Comma, Quad, Sp,
                Call("M", F.Id("v")), Eq, Max, Open, mean, Comma, a, Close, Comma),
            Seq(Amp, Forall, Sp, readout, Colon, Sp, F.Id("I"), Sp, To, Sp, Mathbb, Grp(F.Id("R")), Comma,
                Quad, Sp, sum, w, Eq, D(1), Sp, Longrightarrow, Sp),
            Seq(Amp, gap, Eq, energyDistance, Plus, Frac, Grp(D(2)), Grp(z), Open,
                t, Open, momentGap, Close, Plus, sum, positive, w, Close, Comma),
            Seq(Amp, Open, Open, Forall, Sp, i, Comma, Sp, w, Sp, Ge, D(0), Close, Sp, Land, Sp, a, Sp,
                Le, Sp, Call("M", readout), Close, Sp, Longrightarrow, Sp, energyDistance, Sp, Le, Sp, gap, Dot)
        ]));
    }
}
