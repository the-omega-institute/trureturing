using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class OccupiedMellinCutoffsDocument : IScribeDocumentDefinition
{
    private static Formula Ratio(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Pow(Formula x, Formula p) => Seq(x, Caret, Grp(p));
    private static Formula A => F.Id("a");
    private static Formula R => F.Id("R");
    private static Formula S => F.Id("s");
    private static Formula Half => Ratio(D(1), D(2));
    private static Formula Reals => Seq(Mathbb, Grp(R));
    private static Formula Exponents => Seq(D(0), Le, Beta, Le, Ratio(D(3), D(4)));
    private static Formula NonnegativeExponent => Seq(D(0), Le, Beta);
    private static Formula Shift => Seq(D(0), Le, Sp, A);
    private static Formula Radius => Seq(D(0), Le, DeltaLower, Le, Half);
    private static Formula BelowCenter => Seq(D(1), Minus, DeltaLower);
    private static Formula AboveCenter => Seq(D(1), Plus, DeltaLower);
    private static Formula Mass(Formula a) => Seq(F.Id("F"), Underscore, Grp(Beta, Comma, a));
    private static Formula MassAt(Formula a) => Seq(Mass(a), Open, S, Close);
    private static Formula Vars(params Formula[] items) => Seq(items);
    private static Formula All(Formula vars, Formula hypotheses, Formula conclusion) =>
        Seq(Open, Forall, Sp, vars, InMacro, Sp, Reals, Comma, Quad,
            hypotheses, Longrightarrow, RowBreak, Grp(), Quad, Sp, conclusion, Close);

    private static Formula Interval(Formula a, Formula l, Formula r, Formula bound) =>
        Seq(Call("IntervalIntegrable", Mass(a), l, r), Sp, Land, Sp,
            Int, Underscore, Grp(l), Caret, Grp(r), MassAt(a), Thin, F.Id("ds"), Le, bound);

    private static Formula TailDomain => Seq(Open, R, Comma, Infty, Close);
    private static Formula TailCutoff => Seq(
        Call("IntegrableOn", Mass(A), TailDomain), Sp, Land, Sp,
        Int, Underscore, Grp(TailDomain), MassAt(A), Thin, F.Id("ds"),
        Le, D(4), Cdot, Sp, Pow(R, Seq(Minus, Half)));

    private static Formula Cutoffs() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        All(Vars(Beta, Comma, A, Comma, DeltaLower),
            Seq(Exponents, Sp, Land, Sp, Shift, Sp, Land, Sp, Radius),
            Interval(A, D(0), DeltaLower, Seq(Ratio(D(6, 4), D(3)), Cdot, Sp,
                Pow(DeltaLower, Ratio(D(3), D(2)))))),
        Sp, Land, RowBreak, Grp(),
        All(Vars(Beta, Comma, DeltaLower), Seq(Exponents, Sp, Land, Sp, Radius),
            Interval(D(0), BelowCenter, AboveCenter,
                Seq(D(3, 2), Cdot, Sp, Pow(DeltaLower, Ratio(D(1), D(4)))))),
        Sp, Land, RowBreak, Grp(),
        All(Vars(Beta, Comma, A, Comma, R),
            Seq(NonnegativeExponent, Sp, Land, Sp, Shift, Sp, Land, Sp, D(2), Le, Sp, R),
            TailCutoff),
        Sp, Land, RowBreak, Grp(),
        All(Vars(Beta, Comma, A, Comma, S), Seq(Exponents, Sp, Land, Sp, Shift,
            Sp, Land, Sp, D(0), Lt, S, Le, Half),
            Seq(MassAt(A), Le, D(3, 2), Cdot, Sp, Pow(S, Half))),
        Sp, Land, RowBreak, Grp(),
        All(Vars(Beta, Comma, A, Comma, S),
            Seq(NonnegativeExponent, Sp, Land, Sp, Shift, Sp, Land, Sp, D(2), Le, Sp, S),
            Seq(MassAt(A), Le, D(2), Cdot, Sp, Pow(S, Seq(Minus, Ratio(D(3), D(2)))))),
        End, Grp(F.Id("gathered"))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Absolute integral bounds control the intervals omitted from the regular Mellin quadrature.",
        H("Cutoffs of the paired Mellin sample"),
        Blocks(Describe.Lean(
            DescribeId.Create("paired-mellin-cutoffs"),
            DeclarationHandle.Create("D5/S1/Words/Patterns/Separable/OccupiedMellinCutoffs.mellin_cutoff_bounds"),
            H("The origin, the center, and the far tail"),
            StatementSource.FromAuthor(Cutoffs()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Write F with subscripts beta and a for the absolute value of the paired sample "
                    + "at exponent beta and shift a. Integrability and all integrals are relative to Lebesgue measure. "
                    + "The center bound uses precisely the unshifted sample; the origin and tail allow any nonnegative shift.")),
                Paragraph(Text(
                    "Near the origin, the first differences cancel and a uniform second-derivative estimate "
                    + "bounds the symmetric numerator by a multiple of the square of the position. Near the center, "
                    + "the absolute numerator is at most the singular power, which can be integrated after reflecting "
                    + "the left half onto the right. Beyond two, all three profile values lie between zero and one. "
                    + "The pointwise bounds at the origin and in the far tail also apply to shifted lattice samples."))),
            DescribeRole.Theorem))));
}
