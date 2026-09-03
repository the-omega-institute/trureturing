using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class OddFiberPoleCertificateDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S1/Recurrence/OddFiberPoleCertificate.odd_fiber_pole_certificate";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An odd-capacity fiber amplitude has a nonzero normalized value of absolute value one "
            + "at v equals minus one.",
        H("Odd Fiber Pole Certificate"),
        Blocks(Describe.Lean(
            DescribeId.Create("odd-fiber-pole-certificate"),
            DeclarationHandle.Create(Declaration),
            H("Odd capacity gives a normalized simple-pole coefficient"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The row amplitude is v^m(1-v^c)/(1-v^2). Away from v equals plus or "
                        + "minus one, multiplying by v+1 cancels exactly one denominator factor "
                        + "and leaves v^m times the finite geometric sum.")),
                Paragraph(Text(
                    "For odd c, Mathlib's neg_one_geom_sum evaluates the geometric factor to one. "
                        + "The normalized value is therefore (-1)^m and has absolute value one, "
                        + "so the factor at minus one is not removable.")),
                Paragraph(Text(
                    "The existing FiberCapacityDivisibility theorem already covers the even "
                        + "capacity criterion and is not duplicated. AlternatingPoleCoefficients "
                        + "concerns a different higher-order power-series coefficient problem."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula() => Disp(Seq(
        F.Id("c"), F.Text, Grp(Sp, F.Id("odd")), Comma, Quad,
        F.Id("r"), Underscore, Grp(F.Id("m,c")), Open, F.Id("v"), Close, Eq,
        Frac,
        Grp(F.Id("v"), Caret, Grp(F.Id("m")), Open, D(1), Minus,
            F.Id("v"), Caret, Grp(F.Id("c")), Close),
        Grp(D(1), Minus, F.Id("v"), Caret, Grp(D(2))), Comma, Quad,
        Operatorname, Grp(F.Id("reg")), Underscore, Grp(F.Id("v=-1")),
        Open, F.Id("r"), Close, Eq, Open, Minus, D(1), Close,
        Caret, Grp(F.Id("m")), Comma, Quad,
        Vert, Sp, Operatorname, Grp(F.Id("reg")), Underscore, Grp(F.Id("v=-1")),
        Open, F.Id("r"), Close, Sp, Vert, Eq, D(1)));
}
