using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DagSemantics;

internal sealed class DependencyAggregateDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DagSemantics/DependencyAggregate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Meet and join aggregates over prerequisite cones are antitone and monotone along "
            + "dependency reachability.",
        H("Dependency Aggregate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prerequisite-meets-are-antitone"),
                DeclarationHandle.Create(Prefix + "prerequisiteMeet_antitone"),
                H("Prerequisite meets decrease downstream"),
                StatementSource.FromAuthor(AggregateFormula("prerequisiteMeet", Leq, true)),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "In a complete lattice, a path from the first node to the second enlarges "
                            + "the second node's prerequisite cone. Meeting over that larger cone "
                            + "can only decrease the aggregate.")),
                    Paragraph(Text(
                        "The displayed path is the sole propositional hypothesis. The complete "
                            + "lattice remains an instance binder, not an added conjunct."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prerequisite-joins-are-monotone"),
                DeclarationHandle.Create(Prefix + "prerequisiteJoin_mono"),
                H("Prerequisite joins increase downstream"),
                StatementSource.FromAuthor(AggregateFormula("prerequisiteJoin", Leq, false)),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For the same reachable pair, every label contributing to the upstream "
                            + "join also contributes to the downstream join.")),
                    Paragraph(Text(
                        "Therefore the first join is below the second. No strict inequality or "
                            + "finiteness of the prerequisite cone is claimed."))),
                DescribeRole.Theorem))));

    private static Formula AggregateFormula(string aggregateName, Formula order, bool reverse)
    {
        Formula edge = F.Id("edge");
        Formula label = F.Id("label");
        Formula first = F.Id("first");
        Formula second = F.Id("second");
        Formula left = Call(aggregateName, edge, label, reverse ? second : first);
        Formula right = Call(aggregateName, edge, label, reverse ? first : second);

        return Disp(Seq(
            Forall, Sp, edge, Colon, Sp,
            F.Id("V"), Sp, To, Sp, F.Id("V"), Sp, To, Sp, F.Id("Prop"), Comma, Sp,
            label, Colon, Sp, F.Id("V"), Sp, To, Sp, F.Id("Label"), Comma,
            RowBreak, Grp(), first, Comma, Sp, second, Colon, Sp, F.Id("V"), Comma, Sp,
            OpenBracket, Call("CompleteLattice", F.Id("Label")), CloseBracket,
            Comma, RowBreak, Grp(),
            Call("ReflTransGen", edge, first, second), Sp, Rightarrow, RowBreak, Grp(),
            left, Sp, order, Sp, right, Dot));
    }
}
