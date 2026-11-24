using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class ActiveCosineConstraintsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/ActiveCosineConstraints";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both cosine moment bounds are tight at every joint minimum of the squared mass on a finite cycle.",
        H("Two active cosine moment constraints"),
        Blocks(
            Paragraph(Text(
                "On residues modulo q set cₖ = cos(2πk/q) and dₖ = cos(4πk/q). "
                + "Let M and N be moments against c and d respectively. "
                + "At a common target a, C(w), D(w), and J(w) mean that w minimizes "
                + "the sum of squared weights over probability laws subject to the first bound, "
                + "the second bound, and both bounds, respectively. Each bound is a lower bound a.")),
            Describe.Lean(
                DescribeId.Create("active-cosine-constraints"),
                DeclarationHandle.Create(Owner + ".active_cosine_constraints"),
                H("Strict cross-moment failure and joint tightness"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The one-moment law is a normalized clipped affine function of its own readout. "
                        + "For the first moment, c−d = (1−c)(2c+1). Both readouts have mean zero, "
                        + "so one can subtract the clipped value at −1/2. The resulting summands are nonnegative "
                        + "and the residue 1 gives a positive term.")),
                    Paragraph(Text(
                        "For the second moment on an even cycle, translation by a half-turn fixes d and negates c. "
                        + "On an odd cycle, doubling is a permutation, so the sum of squared clipped values "
                        + "is unchanged. Each squared positive-part tangent defect is nonnegative, "
                        + "and residue 1 supplies strict inequality.")),
                    Paragraph(Text(
                        "If one bound had slack at a joint minimum, a small mixture with the minimizer for "
                        + "the other bound would still satisfy both bounds and would decrease the squared mass."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var q = F.Id("q");
        var a = F.Id("a");
        var w = F.Id("w");
        var reals = Seq(Mathbb, Grp(F.Id("R")));
        var domain = Seq(Mathbb, Grp(F.Id("Z")), Slash, q, Mathbb, Grp(F.Id("Z")), Sp, To, Sp, reals);
        var m = Call("M", w);
        var n = Call("N", w);
        return Disp(new Formula.Aligned([
            Seq(Amp, Forall, Sp, q, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Quad, Sp,
                q, Sp, Ge, Sp, D(4), Comma, Quad, Sp,
                Forall, Sp, a, Sp, InMacro, Sp, reals, Comma, Quad, Sp, D(0), Lt, a, Lt, D(1), Colon),
            Seq(Amp, Forall, Sp, w, Colon, domain, Comma, Quad, Sp, Call("C", w), Sp, Longrightarrow, Sp,
                m, Eq, a, Sp, Land, Sp, n, Lt, a, Comma),
            Seq(Amp, Forall, Sp, w, Colon, domain, Comma, Quad, Sp, Call("D", w), Sp, Longrightarrow, Sp,
                n, Eq, a, Sp, Land, Sp, m, Lt, a, Comma),
            Seq(Amp, Forall, Sp, w, Colon, domain, Comma, Quad, Sp, Call("J", w), Sp, Longrightarrow, Sp,
                m, Eq, a, Sp, Land, Sp, n, Eq, a, Dot)
        ]));
    }
}
