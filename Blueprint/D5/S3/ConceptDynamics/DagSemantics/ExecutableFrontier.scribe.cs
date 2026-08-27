using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DagSemantics;

internal sealed class ExecutableFrontierDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DagSemantics/ExecutableFrontier.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The executable frontier consists of pending nodes whose direct prerequisites are "
            + "complete.",
        H("Executable Frontier"),
        Blocks(Describe.Lean(
            DescribeId.Create("complement-frontier-characterization"),
            DeclarationHandle.Create(Prefix + "mem_frontier_complement_iff"),
            H("The complement frontier is exactly the ready pending set"),
            StatementSource.FromAuthor(FrontierFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A node belongs to the frontier computed over the complement of pending "
                        + "exactly when it is pending and none of its direct prerequisites remain "
                        + "pending.")),
                Paragraph(Text(
                    "The equivalence unfolds the definitions of executableFrontier and ReadyOver. "
                        + "It concerns direct prerequisites and does not replace them with "
                        + "arbitrary "
                        + "reachable ancestors."))),
            DescribeRole.Theorem))));

    private static Formula FrontierFormula()
    {
        Formula edge = F.Id("edge");
        Formula pending = F.Id("pending");
        Formula node = F.Id("node");
        Formula prerequisite = F.Id("prerequisite");
        Formula right = Seq(
            node, Sp, InMacro, Sp, pending, Sp, Land, Sp,
            Forall, Sp, prerequisite, Colon, Sp, F.Id("V"), Comma, Sp,
            Call("edge", prerequisite, node), Sp, Rightarrow, Sp,
            Neg, Sp, Open, prerequisite, Sp, InMacro, Sp, pending, Close);

        return Disp(Seq(
            Forall, Sp, edge, Colon, Sp,
            F.Id("V"), Sp, To, Sp, F.Id("V"), Sp, To, Sp, F.Id("Prop"), Comma, Sp,
            pending, Colon, Sp, Call("Set", F.Id("V")), Comma, Sp,
            node, Colon, Sp, F.Id("V"), Comma, RowBreak, Grp(),
            node, Sp, InMacro, Sp,
            Call("executableFrontier", edge, Call("complement", pending), pending),
            Sp, Iff, RowBreak, Grp(), Open, right, Close, Dot));
    }
}
