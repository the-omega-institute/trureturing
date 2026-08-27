using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Appeal;

internal sealed class MinimalAppealLabelCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Maximum target diversity in a record fiber is the exact appeal label count.",
        H("Minimal Appeal Label Count"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("minimal-appeal-label-count"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Appeal/MinimalAppealLabelCount."
                        + "minimal_appeal_label_count"),
                H("Fiber diversity gives the exact number of appeal labels"),
                StatementSource.FromAuthor(MinimalLabelFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let d be the largest number of distinct target outcomes realized in "
                            + "any one record fiber. The state and record carriers are finite, "
                            + "while the target carrier itself need not be finite.")),
                    Paragraph(Text(
                        "There is a label with d possible values that makes the target exact "
                            + "once the original record is fixed. It is obtained by indexing the "
                            + "realized target outcomes inside each fiber, and the same labels may "
                            + "be reused in different fibers.")),
                    Paragraph(Text(
                        "Conversely, any exact label with m possible values is injective on one "
                            + "representative of each realized target outcome in every fiber. "
                            + "Each fiber therefore has at most m target outcomes, so d is at "
                            + "most m. Together the two directions make d the exact minimum."))),
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

    private static Formula MinimalLabelFormula()
    {
        Formula state = F.Id("X");
        Formula recordCarrier = F.Id("B");
        Formula targetCarrier = F.Id("Y");
        Formula record = F.Id("r");
        Formula target = F.Id("t");
        Formula diversity = Call("worstFiberDiversity", record, target);
        Formula exactLabel = new Formula.Subscript(F.Id("ell"), F.Id("exact"));
        Formula candidateLabel = new Formula.Subscript(F.Id("ell"), F.Id("candidate"));
        Formula labelCount = F.Id("m");
        Formula naturalNumbers = Seq(Mathbb, Grp(F.Id("N")));

        Formula Fin(Formula size) => Call("Fin", size);
        Formula Determines(Formula label) =>
            Call("AppealDetermines", record, target, label);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, recordCarrier, Comma, Sp, targetCarrier,
            Colon, Sp, F.Id("Type"), Comma, RowBreak, Grp(),
            Fintype(state), Comma, Sp, Fintype(recordCarrier), Comma, RowBreak, Grp(),
            record, Colon, Sp, state, Sp, To, Sp, recordCarrier, Comma, Sp,
            target, Colon, Sp, state, Sp, To, Sp, targetCarrier, Comma,
            RowBreak, Grp(),
            Open, Exists, Sp, exactLabel, Colon, Sp, state, Sp, To, Sp,
            Fin(diversity), Comma, Sp, Determines(exactLabel), Close,
            Sp, Land, Sp, RowBreak, Grp(),
            Open, Forall, Sp, labelCount, Colon, Sp, naturalNumbers,
            Comma, Sp, candidateLabel, Colon, Sp, state, Sp, To, Sp,
            Fin(labelCount), Comma, RowBreak, Grp(),
            Determines(candidateLabel), Sp, Rightarrow, Sp,
            diversity, Sp, Leq, Sp, labelCount, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
