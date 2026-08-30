using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GovernanceFixedPoint;

internal sealed class ConservativeChannelAdditionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/GovernanceFixedPoint/ConservativeChannelAddition.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every deadlocked repair class can be added as an exact conservative channel.",
        H("Conservative Channel Addition"),
        Blocks(Describe.Lean(
            DescribeId.Create("conservative-channel-exists"),
            DeclarationHandle.Create(Prefix + "conservative_channel_exists"),
            H("A conservative channel exists for every deadlocked repair class"),
            StatementSource.FromAuthor(ChannelFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The explicit channel is the repair class itself. Deadlock makes that class "
                    + "disjoint from the old joint allowance, so adjoining the channel "
                    + "preserves every old allowance and adds exactly the repair class."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula ChannelFormula()
    {
        Formula repairType = F.Id("Repair");
        Formula repairClass = F.Id("repairClass");
        Formula allowFirst = Seq(F.Id("allow"), Underscore, Grp(D(1)));
        Formula allowSecond = Seq(F.Id("allow"), Underscore, Grp(D(2)));
        Formula channel = F.Id("channel");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula setType = Apply(F.Id("Set"), repairType);

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Typed(repairType, type), Comma),
            Seq(
                Forall, Sp,
                Typed(
                    Seq(repairClass, Comma, Sp, allowFirst, Comma, Sp, allowSecond),
                    setType),
                Comma, RowBreak, Grp()),
            Seq(
                Apply(F.Id("Deadlocked"), repairClass, allowFirst, allowSecond),
                Sp, Rightarrow, Sp),
            Seq(
                Exists, Sp, Typed(channel, setType), Comma, RowBreak, Grp()),
            Seq(
                Apply(
                    F.Id("ConservativeChannel"),
                    repairClass, allowFirst, allowSecond, channel),
                Dot),
        ]));
    }
}
