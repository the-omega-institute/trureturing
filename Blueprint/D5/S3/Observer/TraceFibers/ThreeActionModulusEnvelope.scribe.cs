using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.TraceFibers;

internal sealed class ThreeActionModulusEnvelopeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The three-action Fibonacci fiber has seven matrix coefficient shapes, with two "
            + "non-dominated shapes whose scalar envelopes cross at one tolerance.",
        H("Three Action Modulus Envelope"),
        Blocks(Describe.Lean(
            DescribeId.Create("three-action-modulus-envelope"),
            DeclarationHandle.Create("D5/S3/Observer/TraceFibers/ThreeActionModulusEnvelope.three_action_modulus_envelope"),
            H("Three-action scalar envelope"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For words of length at most three in the advance and exchange actions, "
                        + "the pair consisting of the diagonal difference and lower-left entry "
                        + "has exactly seven possible values. The positive-entry injective shapes "
                        + "are (1,1), (2,1), and (2,2); the latter two are represented by MJM and MMM, "
                        + "while (1,1) is represented by the shorter compatible words.")),
                Paragraph(Text(
                    "Writing d for a source spacing, the two distinguished scalar separation "
                        + "functions are phi_S(d)=(2-h)d+d^2/r and "
                        + "phi_A(d)=(2-2h)d+2d^2/r. Their difference is "
                        + "d(d/r-h), so their common spacing is rh and their common tolerance is 2rh.")),
                Paragraph(Text(
                    "The endpoint values of the two quadratic separation functions are ordered "
                        + "by k and h, while the common spacing is rh. The inverse-envelope "
                        + "root is supplied by the fixed-fiber modulus interface."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula k = F.Id("k");
        Formula h = F.Id("h");
        Formula x = F.Id("x");
        Formula r = F.Id("r");
        Formula d = F.Id("d");
        Formula tau = F.Id("tau");
        Formula tauStar = F.Id("tauStar");
        Formula dStar = F.Id("dStar");
        Formula ts = F.Id("TS");
        Formula ta = F.Id("TA");
        return Disp(new Formula.Aligned([
            Seq(k, Sp, Ge, Sp, D(1), Comma, Sp, D(0), Sp, Lt, Sp, h, Sp, Lt, Sp, D(1),
                Comma, Sp, x, Sp, Eq, Sp, Grp(k, Plus, h), Cdot, Sp, r),
            Seq(tauStar, Sp, Eq, Sp, D(2), Cdot, Sp, r, Cdot, Sp, h, Comma, Sp,
                dStar, Sp, Eq, Sp, r, Cdot, Sp, h),
            Seq(ts, Sp, Eq, Sp, Grp(k, Plus, D(2)), Cdot, Sp, x, Comma, Sp,
                ta, Sp, Eq, Sp, D(2), Cdot, Sp, Grp(k, Plus, D(1)), Cdot, Sp, x),
            Seq(F.Id("phiA"), Sp, Minus, Sp, F.Id("phiS"), Sp, Eq, Sp,
                d, Cdot, Sp, Grp(new Formula.Fraction(Seq(d, Minus, r, Cdot, Sp, h), r))),
            Seq(tauStar, Sp, Lt, Sp, ts, Sp, Lt, Sp, ta),
            Seq(F.Id("d"), Sp, Eq, Sp, dStar, Sp, Rightarrow, Sp,
                F.Id("phiA"), Sp, Eq, Sp, F.Id("phiS"), Sp, Eq, Sp, tauStar)
        ]));
    }
}
