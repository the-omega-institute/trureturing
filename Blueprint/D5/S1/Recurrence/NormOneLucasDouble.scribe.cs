using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class NormOneLucasDoubleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A pair whose product is one satisfies trace and discriminant-weighted companion "
            + "doubling identities in a commutative ring.",
        H("Norm-One Trace and Companion Doubling Identities"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("norm-one-lucas-double-trace-square"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/NormOneLucasDouble.trace_sq_eq_trace_two_mul_add_two"),
                H("Square of the trace expression"),
                StatementSource.FromAuthor(TraceSquareFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The cross term is a^n * b^n = (a * b)^n = 1. Expanding the "
                            + "square and rewriting each square of an n-th power at index "
                            + "2 * n therefore leaves the doubled-index sum plus two.")),
                    Paragraph(Text(
                        "All Lucas results frozen in this repository concern the specific "
                            + "golden-ratio instance, whose discriminant is five; this module "
                            + "proves the general form for an arbitrary norm-one conjugate pair "
                            + "and makes no new assertion about that existing instance."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("norm-one-lucas-double-companion-square"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/NormOneLucasDouble."
                        + "companion_sq_eq_trace_two_mul_sub_two"),
                H("Weighted square of the companion expression"),
                StatementSource.FromAuthor(CompanionSquareFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Again, the cross term reduces through a^n * b^n = (a * b)^n = 1. "
                            + "Squaring the entire equation (a - b) * u = a^n - b^n and "
                            + "substituting it into the expanded square gives the "
                            + "doubled-index sum minus two.")),
                    Paragraph(Text(
                        "The argument uses only commutative-ring identities and the two stated "
                            + "equations; it makes no classification or arithmetic claim beyond "
                            + "the displayed identity."))),
                DescribeRole.Theorem))));

    private static Formula TraceSquareFormula()
    {
        Formula ring = F.Id("R");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula n = F.Id("n");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Context(ring),
            Forall, Sp, a, Comma, Sp, b, Colon, Sp, ring, Comma, RowBreak,
            Grp(a, Sp, Cdot, Sp, b, Sp, Eq, Sp, Num(1)), Sp, Implies, RowBreak,
            Forall, Sp, n, Colon, Sp, NaturalNumbers(), Comma, RowBreak,
            Power(Seq(Power(a, n), Sp, Plus, Sp, Power(b, n)), Num(2)), Sp,
            Eq, Sp,
            Grp(
                Power(a, DoubleIndex(n)), Sp, Plus, Sp,
                Power(b, DoubleIndex(n))),
            Sp, Plus, Sp, Num(2), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula CompanionSquareFormula()
    {
        Formula ring = F.Id("R");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula u = F.Id("u");
        Formula n = F.Id("n");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Context(ring),
            Forall, Sp, a, Comma, Sp, b, Comma, Sp, u, Colon, Sp, ring, Comma, RowBreak,
            Grp(a, Sp, Cdot, Sp, b, Sp, Eq, Sp, Num(1)), Sp, Implies, RowBreak,
            Forall, Sp, n, Colon, Sp, NaturalNumbers(), Comma, RowBreak,
            Grp(
                Grp(a, Sp, Minus, Sp, b), Sp, Cdot, Sp, u, Sp, Eq, Sp,
                Power(a, n), Sp, Minus, Sp, Power(b, n)),
            Sp, Implies, RowBreak,
            Power(Seq(a, Sp, Minus, Sp, b), Num(2)), Sp, Cdot, Sp,
            Power(u, Num(2)), Sp, Eq, Sp,
            Grp(
                Power(a, DoubleIndex(n)), Sp, Plus, Sp,
                Power(b, DoubleIndex(n))),
            Sp, Minus, Sp, Num(2), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Context(Formula ring) =>
        Seq(
            Forall, Sp, ring, Colon, Sp, F.Id("Type"), Comma, Sp,
            TypeClass(Call("CommRing", ring)), Comma, RowBreak);

    private static Formula DoubleIndex(Formula n) =>
        Seq(Num(2), Sp, Cdot, Sp, n);

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(Grp(value), Caret, Grp(exponent));

    private static Formula NaturalNumbers() =>
        Seq(Mathbb, Grp(F.Id("N")));

    private static Formula TypeClass(Formula value) =>
        Seq(OpenBracket, value, CloseBracket);
}
