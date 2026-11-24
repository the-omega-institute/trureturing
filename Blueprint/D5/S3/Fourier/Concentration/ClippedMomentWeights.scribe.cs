using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class ClippedMomentWeightsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/ClippedMomentWeights";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A normalized positive part attains a prescribed real moment at minimum squared mass.",
        H("Minimum squared mass with one lower moment bound"),
        Blocks(Describe.Lean(
            DescribeId.Create("clipped-moment-minimizer"),
            DeclarationHandle.Create(Owner + ".exists_clipped_moment_minimizer"),
            H("Exact optimizer for one real lower moment bound"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The indices form a finite set I. The readout c is real, C is its attained "
                    + "maximum, and a lies between the mean of c under the uniform law and C. "
                    + "All sums range over I. The last line holds for every nonnegative w with "
                    + "sum one and moment at least a.")),
                Paragraph(Text(
                    "At t = 0 the weights are uniform. Every index attaining the maximum "
                    + "has raw weight one for every t, so the normalization stays positive. "
                    + "At one plus the sum of the reciprocals of the positive gaps C − cᵢ, "
                    + "every submaximal index has weight zero. The normalized moment is "
                    + "continuous between these endpoints, so it attains a at a finite t.")),
                Paragraph(Text(
                    "Write the raw affine weights as 1 − t(C − cᵢ). Their inner product "
                    + "with w − v is nonnegative because the masses agree and the moment of "
                    + "w is at least that of v. Taking positive parts can only increase this "
                    + "inner product. At each clipped index v vanishes and w is nonnegative. "
                    + "After normalization, expand the squared norm around v. The lower "
                    + "bound by the squared distance forces uniqueness.")),
                Paragraph(Text(
                    "For cyclic Fourier weights, cᵢ can be the real part of a character "
                    + "at a single spatial residue. The resulting squared mass is the "
                    + "minimum with this one constraint. A whole spatial band imposes further "
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
        return Disp(new Formula.Aligned([
            Seq(Amp, Frac, Grp(sum, c), Grp(Bar, F.Id("I"), Bar), Sp, Le, Sp, a, Sp, Le, Sp, cap,
                Comma, Quad, Sp, Exists, Sp, t, Sp, Ge, D(0), Comma),
            Seq(Amp, u, Eq, Max, Open, D(0), Comma, D(1), Minus, t, Open, cap, Minus, c, Close, Close,
                Comma, Quad, Sp, v, Eq, Frac, Grp(u), Grp(new Formula.Subscript(Sum, j), uj), Comma),
            Seq(Amp, v, Sp, Ge, D(0), Comma, Quad, Sp, sum, v, Eq, D(1), Comma, Quad, Sp,
                sum, v, c, Eq, a, Comma),
            Seq(Amp, sum, new Formula.Power(Seq(Open, w, Minus, v, Close), D(2)), Sp, Le, Sp,
                sum, new Formula.Power(w, D(2)), Minus, sum, new Formula.Power(v, D(2)), Dot)
        ]));
    }
}
