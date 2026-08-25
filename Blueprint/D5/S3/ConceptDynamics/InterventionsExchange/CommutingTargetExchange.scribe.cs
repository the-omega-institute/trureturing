using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InterventionsExchange;

internal sealed class CommutingTargetExchangeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Commuting state interventions have an empty target-level order-defect set.",
        H("Commuting Target Exchange"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("commutation-defect"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/InterventionsExchange/CommutingTargetExchange."
                        + "commutationDefect"),
                H("Target-level intervention defect"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For two state maps and a target readout, the commutation defect is "
                            + "the set of states whose target values differ after the two "
                            + "orders of composition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("commuting-target-defect-empty"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/InterventionsExchange/CommutingTargetExchange."
                        + "commuting_target_defect_empty"),
                H("Commuting maps have no target defect"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source state carrier, two intervention maps, and target readout "
                            + "are independent primitives. The public premise is equality of "
                            + "the two composite maps.")),
                    Paragraph(Text(
                        "The conclusion exposes the source Comm object directly as the empty "
                            + "set. It follows by applying the target to the composite-map "
                            + "equality pointwise.")),
                    Paragraph(Text(
                        "The defect set is constructed from the two source compositions before "
                            + "the theorem; it is not defined as the empty target.")),
                    Paragraph(Text(
                        "No exact repository theorem packages this general target-level empty "
                            + "defect statement. The canonical Concept carrier and elementary "
                            + "set equality are used directly."))),
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

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula targetType = F.Id("Y");
        Formula first = F.Id("F");
        Formula second = F.Id("G");
        Formula target = F.Id("T");
        Formula map = Seq(state, Sp, To, Sp, state);
        Formula readout = Seq(state, Sp, To, Sp, targetType);
        Formula defect = Call("commutationDefect", first, second, target);
        return Disp(Seq(
            Forall, Sp, state, Comma, Sp, targetType, Comma, RowBreak, Grp(),
            first, Comma, Sp, second, Colon, Sp, map, Comma, Sp,
            target, Colon, Sp, readout, Comma, RowBreak, Grp(),
            first, Sp, Circ, Sp, second, Sp, Eq, Sp,
            second, Sp, Circ, Sp, first, Sp, Rightarrow, RowBreak, Grp(),
            defect, Sp, Eq, Sp, Emptyset, Dot));
    }
}
