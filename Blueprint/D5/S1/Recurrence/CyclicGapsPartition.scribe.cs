using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class CyclicGapsPartitionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Recurrence/CyclicGapsPartition",
                "Positive cyclic gaps partition the unit circle."),
            H("Cyclic Gap Partition"),
            Blocks(
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("cyclic-gaps-partition-circle"),
                    H("Cyclic gaps partition the circle"),
                    LeanTheorem(
                        "D5/S1/Recurrence/CyclicGapsPartition."
                        + "cyclic_gaps_partition_circle"),
                    Disp(Seq(Forall, Sp, F.Id("S"), Subseteq, OpenBracket, D(0), Comma, D(1), Close, Esc, F.Text, Grp(F.Id("finite")), Comma, Esc, F.Id("S"), Neq, Emptyset, Comma, Esc, F.Id("g"), Underscore, F.Id("S"), Open, F.Id("x"), Close, Eq, Begin, Grp(F.Id("cases")), Open, D(1), Minus, F.Id("x"), Close, Plus, Min, Sp, F.Id("S"), Comma, Amp, F.Id("x"), Eq, Max, Sp, F.Id("S"), RowBreak, Operatorname, Grp(F.Id("succ")), Underscore, F.Id("S"), Open, F.Id("x"), Close, Minus, F.Id("x"), Comma, Amp, F.Id("x"), Neq, Max, Sp, F.Id("S"), End, Grp(F.Id("cases")), Colon, Esc, Open, Forall, Sp, F.Id("x"), InMacro, Sp, F.Id("S"), Comma, Esc, Operatorname, Grp(F.Id("succ")), Underscore, F.Id("S"), Open, F.Id("x"), Close, InMacro, Sp, F.Id("S"), Close, Esc, Land, Esc, Open, Forall, Sp, F.Id("x"), InMacro, Sp, F.Id("S"), Comma, Esc, F.Id("g"), Underscore, F.Id("S"), Open, F.Id("x"), Close, Gt, D(0), Close, Esc, Land, Esc, Sum, Underscore, Grp(F.Id("x"), InMacro, Sp, F.Id("S")), F.Id("g"), Underscore, F.Id("S"), Open, F.Id("x"), Close, Eq, D(1))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "For a nonempty finite subset of the half-open unit interval, each "
                        + "cyclic successor remains in the subset and every clockwise gap is "
                        + "strictly positive. The successor and predecessor are inverse "
                        + "permutations of the subset, so successor terms cancel against the "
                        + "original points in the total sum. The unique wrap correction then "
                        + "contributes exactly one, and all gaps sum to the circumference.")))))));
}
