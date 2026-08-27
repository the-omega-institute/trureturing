using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DagCompletion;

internal sealed class WellFoundedFrontierDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DagCompletion/WellFoundedFrontier.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every nonempty pending set has an executable node under a well-founded prerequisite "
            + "relation.",
        H("Well-Founded Frontier"),
        Blocks(Describe.Lean(
            DescribeId.Create("well-founded-pending-set-has-frontier"),
            DeclarationHandle.Create(Prefix + "complement_frontier_nonempty_of_wellFounded"),
            H("A well-founded nonempty pending set has a frontier node"),
            StatementSource.FromAuthor(FrontierFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Assume the prerequisite relation is well-founded and the pending set is "
                        + "nonempty. A minimal pending element has no pending prerequisite.")),
                Paragraph(Text(
                    "That element witnesses nonemptiness of the executable frontier over the "
                        + "pending complement. No finiteness or linear order is assumed."))),
            DescribeRole.Theorem))));

    private static Formula FrontierFormula()
    {
        Formula edge = F.Id("edge");
        Formula pending = F.Id("pending");
        Formula hypotheses = Seq(
            Call("WellFounded", edge), Sp, Land, Sp, Call("Nonempty", pending));

        return Disp(Seq(
            Forall, Sp, edge, Colon, Sp,
            F.Id("V"), Sp, To, Sp, F.Id("V"), Sp, To, Sp, F.Id("Prop"), Comma, Sp,
            pending, Colon, Sp, Call("Set", F.Id("V")), Comma, RowBreak, Grp(),
            Open, hypotheses, Close, Sp, Rightarrow, RowBreak, Grp(),
            Call("Nonempty", Call("executableFrontier", edge,
                Call("complement", pending), pending)), Dot));
    }
}
