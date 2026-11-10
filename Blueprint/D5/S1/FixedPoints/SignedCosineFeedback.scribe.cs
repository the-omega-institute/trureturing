using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.FixedPoints;

internal sealed class SignedCosineFeedbackDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Dottie =
        LibraryNoteRef.Create("D5/L/FixedPoints/kaplan2007dottie");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For either sign s the map sending x to s cos x has exactly one real fixed point, namely s r with r in the open unit interval and cos r = r, and every real orbit approaches it with error ratio at most sin 1; with freely chosen signs the absolute values still converge to r.",
        H("Signed Cosine Feedback"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("signed-cosine-feedback-has-one-real-fixed-point"),
                DeclarationHandle.Create(
                    "D5/S1/FixedPoints/SignedCosineFeedback."
                        + "signed_cosine_feedback_fixed_point"),
                H("Signed cosine feedback: fixed point, contraction and sign policies"),
                StatementSource.FromAuthor(FixedPointFormula()),
                AssessedProvenance.FromRepo(Dottie),
                Blocks(
                    Paragraph(Text(
                        "Write F(x) = s cos x for a sign s equal to 1 or to -1. The "
                            + "theorem produces one number r strictly between 0 and 1 with "
                            + "cos r = r, and no other number of that interval solves the "
                            + "equation. Taking s = 1 in the fixed-point clause shows more: "
                            + "r is the only real solution of cos x = x.")),
                    Paragraph(Text(
                        "For either sign, s r is the only real fixed point of F, every "
                            + "value F(x) lies in the closed interval from -1 to 1, and on "
                            + "that interval F multiplies the distance between two points "
                            + "by at most sin 1. The orbit of an arbitrary real x satisfies the "
                            + "displayed error bound: after the first step the distance to "
                            + "s r is multiplied by at most sin 1 at every further step. "
                            + "Since sin 1 is positive and less than 1, the orbit converges "
                            + "to s r.")),
                    Paragraph(Text(
                        "The function cos x - x is positive at 0 and negative at 1, so it "
                            + "vanishes between them. On the closed interval from -1 to 1 "
                            + "the identity cos x - cos y = -2 sin((x + y)/2) sin((x - y)/2), "
                            + "the bound of the sine by sin 1 on that interval and the bound "
                            + "of sin v by v in absolute value give that two cosine values "
                            + "differ by at most sin 1 times the distance of their arguments. "
                            + "The cosine is even, so F fixes s r. A real fixed point x of F "
                            + "lies in the interval, and the estimate applied to x and s r "
                            + "bounds their distance by sin 1 times itself, which forces "
                            + "x = s r. Applied along an orbit it gives the error bound.")),
                    Paragraph(Text(
                        "A common solution of cos x = x and cos x = -x would satisfy "
                            + "x = -x, hence x = 0, although cos 0 = 1. Any map G with "
                            + "G(s, x) = (-s, -s cos x) for the two signs s sends (1, r) to "
                            + "(-1, -r) and back, and these two points differ in their "
                            + "first coordinate, so they form an orbit of period exactly "
                            + "two.")),
                    Paragraph(Text(
                        "Now let the sign be chosen freely at every step, so that each "
                            + "term of a real sequence is plus or minus the cosine of the "
                            + "previous term. From the second term on, every term lies in "
                            + "the closed interval from -1 to 1, where the cosine is "
                            + "nonnegative and even; hence the absolute value of the next "
                            + "term is the cosine of the absolute value of the current one. "
                            + "The absolute values therefore follow the cosine orbit and "
                            + "converge to r. The signs need not settle: the sequence "
                            + "r, -r, r, -r, ... obeys the rule and changes sign at every "
                            + "step.")),
                    Paragraph(Text(
                        "The number r is the Dottie number. That it is the only real "
                            + "fixed point of the cosine and the limit of every real cosine "
                            + "orbit is classical; the statement here also records the "
                            + "ratio sin 1, the mirror map with fixed point -r, the orbit "
                            + "of period two, and the behaviour under freely chosen "
                            + "signs."))),
                DescribeRole.Theorem))));

    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Cos(Formula argument) =>
        Seq(Operatorname, Grp(F.Id("cos")), Open, argument, Close);

    private static Formula SinOne => Seq(Sin, Sp, D(1));

    private static Formula Abs(Formula value) => Seq(Lvert, Sp, value, Sp, Rvert);

    private static Formula Pair(Formula first, Formula second) =>
        Seq(Open, first, Comma, Sp, second, Close);

    private static Formula At(Formula sequence, Formula index) =>
        Seq(sequence, Open, index, Close);

    private static Formula Iterate(Formula s, Formula exponent, Formula argument)
    {
        Formula y = F.Id("y");
        return Seq(
            Open, y, Sp, Mapsto, Sp, s, Cos(y), Close, Caret, Grp(exponent),
            Open, argument, Close);
    }

    private static Formula FixedPointFormula()
    {
        Formula r = F.Id("r");
        Formula s = F.Id("s");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula n = F.Id("n");
        Formula g = F.Id("G");
        Formula sigma = SigmaLower;
        Formula unitOpen = Seq(Open, D(0), Comma, Sp, D(1), Close);
        Formula unitClosed = Seq(OpenBracket, Minus, D(1), Comma, Sp, D(1), CloseBracket);
        Formula plane = Seq(Reals, Sp, Times, Sp, Reals);
        Formula sr = Seq(s, r);
        Formula minusOne = Seq(Minus, D(1));
        Formula minusR = Seq(Minus, r);
        Formula isSign = Seq(Open, s, Eq, D(1), Sp, Lor, Sp, s, Eq, minusOne, Close);
        Formula sequences = Seq(
            sigma, Comma, Sp, x, Colon, Sp, Naturals, To, Sp, Reals);
        Formula signRule = Seq(
            Open, Forall, Sp, n, InMacro, Sp, Naturals, Comma, Sp,
            At(sigma, n), Eq, D(1), Sp, Lor, Sp, At(sigma, n), Eq, minusOne, Close);
        Formula stepRule = Seq(
            Open, Forall, Sp, n, InMacro, Sp, Naturals, Comma, Sp,
            At(x, Seq(n, Plus, D(1))), Eq, At(sigma, n), Cos(At(x, n)), Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Exists, Sp, r, InMacro, Sp, Reals, Comma, Sp,
            r, InMacro, Sp, unitOpen, Sp, Land, Sp, Cos(r), Eq, r, Sp, Land, RowBreak,
            Open, Forall, Sp, y, InMacro, Sp, unitOpen, Comma, Sp,
            Cos(y), Eq, y, Sp, Rightarrow, Sp, y, Eq, r, Close, Sp, Land, Sp,
            D(0), Lt, SinOne, Sp, Land, Sp, SinOne, Lt, D(1), Sp, Land, RowBreak,
            Open, Forall, Sp, s, InMacro, Sp, Reals, Comma, Sp,
            isSign, Sp, Rightarrow, RowBreak,
            Open, Forall, Sp, x, InMacro, Sp, Reals, Comma, Sp,
            s, Cos(x), Eq, x, Sp, Leftrightarrow, Sp, x, Eq, sr, Close, Sp, Land, Sp,
            Open, Forall, Sp, x, InMacro, Sp, Reals, Comma, Sp,
            s, Cos(x), InMacro, Sp, unitClosed, Close, Sp, Land, RowBreak,
            Open, Forall, Sp, x, InMacro, Sp, unitClosed, Comma, Sp,
            Forall, Sp, y, InMacro, Sp, unitClosed, Comma, Sp,
            Abs(Seq(s, Cos(x), Minus, s, Cos(y))), Leq, Sp,
            SinOne, Sp, Abs(Seq(x, Minus, y)), Close, Sp, Land, RowBreak,
            Open, Forall, Sp, x, InMacro, Sp, Reals, Comma, Sp,
            Forall, Sp, n, InMacro, Sp, Naturals, Comma, Sp,
            Abs(Seq(Iterate(s, Seq(n, Plus, D(1)), x), Minus, sr)), Leq, Sp,
            Open, SinOne, Close, Caret, Grp(n),
            Abs(Seq(s, Cos(x), Minus, sr)), Close, Sp, Land, RowBreak,
            Open, Forall, Sp, x, InMacro, Sp, Reals, Comma, Sp,
            Lim, Underscore, Grp(n, To, Infty), Sp, Iterate(s, n, x), Eq, sr,
            Close, Close, Sp, Land, RowBreak,
            Neg, Sp, Open, Exists, Sp, x, InMacro, Sp, Reals, Comma, Sp,
            Cos(x), Eq, x, Sp, Land, Sp, Cos(x), Eq, Minus, x, Close, Sp, Land, RowBreak,
            Open, Forall, Sp, g, Colon, Sp, plane, To, Sp, plane, Comma, Sp,
            Open, Forall, Sp, s, Comma, Sp, x, InMacro, Sp, Reals, Comma, Sp,
            isSign, Sp, Rightarrow, Sp,
            g, Pair(s, x), Eq, Pair(Seq(Minus, s), Seq(Minus, s, Cos(x))), Close,
            Sp, Rightarrow, RowBreak,
            g, Pair(D(1), r), Eq, Pair(minusOne, minusR), Sp, Land, Sp,
            g, Pair(minusOne, minusR), Eq, Pair(D(1), r), Sp, Land, Sp,
            Pair(D(1), r), Neq, Sp, Pair(minusOne, minusR), Close, Sp, Land, RowBreak,
            Open, Forall, Sp, sequences, Comma, Sp,
            signRule, Sp, Rightarrow, Sp, stepRule, Sp, Rightarrow, RowBreak,
            Open, Forall, Sp, n, InMacro, Sp, Naturals, Comma, Sp,
            Abs(At(x, Seq(n, Plus, D(2)))), Eq,
            Cos(Abs(At(x, Seq(n, Plus, D(1))))), Close, Sp, Land, Sp,
            Lim, Underscore, Grp(n, To, Infty), Sp, Abs(At(x, n)), Eq, r,
            Close, Sp, Land, RowBreak,
            Open, Exists, Sp, sequences, Comma, Sp,
            signRule, Sp, Land, Sp, stepRule, Sp, Land, RowBreak,
            Open, Forall, Sp, n, InMacro, Sp, Naturals, Comma, Sp,
            At(x, Seq(n, Plus, D(1))), Eq, Minus, At(x, n), Close, Sp, Land, Sp,
            At(x, D(0)), Eq, r, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
