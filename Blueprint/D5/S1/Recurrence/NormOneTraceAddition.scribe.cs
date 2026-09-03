using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class NormOneTraceAdditionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Norm-one power sums satisfy an addition law and its two-step recurrence.",
        H("Norm-One Trace Addition and Recurrence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("norm-one-trace-addition-trace-add-two-mul"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/NormOneTraceAddition.trace_add_two_mul"),
                H("Trace addition law"),
                StatementSource.FromAuthor(TraceAdditionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Writing T k for a ^ k + b ^ k, shifting the index by twice a step "
                            + "multiplies by the value at that step and subtracts the "
                            + "unshifted term. The law is stated with m + 2 * n rather than "
                            + "a difference of indices so that no truncated subtraction on "
                            + "Nat is needed.")),
                    Paragraph(Text(
                        "The norm-one hypothesis is what makes the identity work: the cross "
                            + "terms of the product collect as (a ^ m + b ^ m) * "
                            + "(a ^ n * b ^ n), and the latter factor is one exactly because "
                            + "a * b = 1.")),
                    Paragraph(Text(
                        "Two cases already exist in this repository: m = 0 is the frozen "
                            + "doubling identity in NormOneLucasDouble, and n = 1 at one "
                            + "concrete real transfer matrix is a private lemma in the "
                            + "Chebyshev transfer-matrix file; neither file is restated or "
                            + "amended."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("norm-one-trace-addition-trace-recurrence"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/NormOneTraceAddition.trace_recurrence"),
                H("Two-step trace recurrence"),
                StatementSource.FromAuthor(TraceRecurrenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "This is the two-step recurrence obtained from the addition law in "
                            + "the case n = 1."))),
                DescribeRole.Theorem))));

    private static Formula TraceAdditionFormula()
    {
        Formula ring = F.Id("R");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula m = F.Id("m");
        Formula n = F.Id("n");
        Formula leftIndex = Seq(m, Sp, Plus, Sp, Num(2), Sp, Cdot, Sp, n);
        Formula middleIndex = Seq(m, Sp, Plus, Sp, n);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Context(ring),
            Parameters(ring, a, b),
            NormOne(a, b), Sp, Implies, RowBreak,
            Forall, Sp, m, Comma, Sp, n, Colon, Sp, NaturalNumbers(), Comma, RowBreak,
            PowerSum(a, b, leftIndex), Sp, Eq, Sp,
            Grp(PowerSum(a, b, middleIndex)), Sp, Cdot, Sp,
            Grp(PowerSum(a, b, n)), Sp, Minus, Sp,
            Grp(PowerSum(a, b, m)), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula TraceRecurrenceFormula()
    {
        Formula ring = F.Id("R");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula m = F.Id("m");
        Formula leftIndex = Seq(m, Sp, Plus, Sp, Num(2));
        Formula nextIndex = Seq(m, Sp, Plus, Sp, Num(1));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Context(ring),
            Parameters(ring, a, b),
            NormOne(a, b), Sp, Implies, RowBreak,
            Forall, Sp, m, Colon, Sp, NaturalNumbers(), Comma, RowBreak,
            PowerSum(a, b, leftIndex), Sp, Eq, Sp,
            Grp(a, Sp, Plus, Sp, b), Sp, Cdot, Sp,
            Grp(PowerSum(a, b, nextIndex)), Sp, Minus, Sp,
            Grp(PowerSum(a, b, m)), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Context(Formula ring) =>
        Seq(
            Forall, Sp, ring, Colon, Sp, F.Id("Type"), Comma, Sp,
            TypeClass(Call("CommRing", ring)), Comma, RowBreak);

    private static Formula Parameters(Formula ring, Formula a, Formula b) =>
        Seq(Forall, Sp, a, Comma, Sp, b, Colon, Sp, ring, Comma, RowBreak);

    private static Formula NormOne(Formula a, Formula b) =>
        Grp(a, Sp, Cdot, Sp, b, Sp, Eq, Sp, Num(1));

    private static Formula PowerSum(Formula a, Formula b, Formula exponent) =>
        Seq(Power(a, exponent), Sp, Plus, Sp, Power(b, exponent));

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(Grp(value), Caret, Grp(exponent));

    private static Formula NaturalNumbers() =>
        Seq(Mathbb, Grp(F.Id("N")));

    private static Formula TypeClass(Formula value) =>
        Seq(OpenBracket, value, CloseBracket);
}
