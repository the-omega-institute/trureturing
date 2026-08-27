using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DagCompletion;

internal sealed class FrontierAntichainDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DagCompletion/FrontierAntichain.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An executable frontier over a predecessor-closed completed set is an antichain for strict "
            + "dependency reachability.",
        H("Frontier Antichain"),
        Blocks(Describe.Lean(
            DescribeId.Create("complement-frontier-is-a-strict-antichain"),
            DeclarationHandle.Create(Prefix + "complement_frontier_strict_antichain"),
            H("The complement frontier is a strict-reachability antichain"),
            StatementSource.FromAuthor(AntichainFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Assume the complement of pending is predecessor-closed, and take two members "
                        + "of the executable frontier computed over that complement.")),
                Paragraph(Text(
                    "No nonempty dependency path can run from the first frontier member to the "
                        + "second. The closure hypothesis is essential and is displayed "
                        + "explicitly."))),
            DescribeRole.Theorem))));

    private static Formula AntichainFormula()
    {
        Formula edge = F.Id("edge");
        Formula pending = F.Id("pending");
        Formula first = F.Id("first");
        Formula second = F.Id("second");
        Formula frontier = Call(
            "executableFrontier", edge, Call("complement", pending), pending);
        Formula hypotheses = Seq(
            Call("PredecessorClosed", edge, Call("complement", pending)),
            Sp, Land, RowBreak, Grp(),
            first, Sp, InMacro, Sp, frontier, Sp, Land, RowBreak, Grp(),
            second, Sp, InMacro, Sp, frontier);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, edge, Colon, Sp,
            F.Id("V"), Sp, To, Sp, F.Id("V"), Sp, To, Sp, F.Id("Prop"), Comma, Sp,
            pending, Colon, Sp, Call("Set", F.Id("V")), Comma, Sp,
            first, Comma, Sp, second, Colon, Sp, F.Id("V"), Comma, RowBreak, Grp(),
            Open, hypotheses, Close, Sp, Rightarrow, RowBreak, Grp(),
            Neg, Sp, Call("TransGen", edge, first, second), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
