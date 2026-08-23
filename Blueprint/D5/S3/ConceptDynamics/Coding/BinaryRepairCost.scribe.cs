using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class BinaryRepairCostDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary repair costs exactly the ceiling binary logarithm of fiber diversity.",
        H("Binary Repair Cost"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("binary-repair-cost-is-log-of-minimal-labels"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Coding/BinaryRepairCost."
                        + "binary_repair_cost_is_log_of_minimal_labels"),
                H("Binary repair width is the logarithm of minimal labels"),
                StatementSource.FromAuthor(RepairCostFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A width-k binary repair label assigns one k-bit string to each state. "
                            + "It determines the target relative to the original record when "
                            + "states with the same record and the same string must have the "
                            + "same target outcome.")),
                    Paragraph(Text(
                        "There are exactly 2^k fixed-width bit strings. Consequently, width k "
                            + "is feasible precisely when this code space is at least as large "
                            + "as the greatest number of distinct target outcomes occurring in "
                            + "one record fiber.")),
                    Paragraph(Text(
                        "The forward direction converts any binary label into a finite label "
                            + "and invokes the minimum-label lower bound. For the reverse "
                            + "direction, a minimum exact label is embedded into the available "
                            + "bit strings, preserving target determination inside every fiber.")),
                    Paragraph(Text(
                        "It follows that the least feasible width is the ceiling logarithm to "
                            + "base two of worst fiber diversity, including the zero-diversity "
                            + "case governed by the natural-number ceiling logarithm."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Fintype(Formula carrier) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, carrier, Close,
            CloseBracket);

    private static Formula RepairCostFormula()
    {
        Formula state = F.Id("X");
        Formula recordCarrier = F.Id("C");
        Formula targetCarrier = F.Id("Target");
        Formula record = F.Id("r");
        Formula target = F.Id("t");
        Formula width = F.Id("k");
        Formula diversity = F.Id("d");
        Formula naturalNumbers = Seq(Mathbb, Grp(F.Id("N")));
        Formula feasible = Call("BinaryRepairFeasible", record, target, width);
        Formula feasibleWidths = Seq(
            OpenBrace, width, Sp, InMacro, Sp, naturalNumbers, Sp, Mid, Sp,
            feasible, CloseBrace);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, recordCarrier, Comma, Sp, targetCarrier,
            Comma, RowBreak, Grp(),
            Fintype(state), Sp, Fintype(recordCarrier), Comma, RowBreak, Grp(),
            record, Colon, Sp, state, Sp, To, Sp, recordCarrier, Comma, Sp,
            target, Colon, Sp, state, Sp, To, Sp, targetCarrier, Comma,
            RowBreak, Grp(),
            diversity, Sp, Eq, Sp, Call("worstFiberDiversity", record, target),
            Comma, RowBreak, Grp(),
            Open, Forall, Sp, width, Sp, InMacro, Sp, naturalNumbers, Comma, Sp,
            feasible, Sp, Iff, Sp,
            diversity, Sp, Leq, Sp, D(2), Caret, Grp(width), Close,
            Sp, Land, RowBreak, Grp(),
            Call("IsLeast", feasibleWidths, Call("clog", D(2), diversity)), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
