using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DagSemantics;

internal sealed class FrontierExtensionClosureDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DagSemantics/FrontierExtensionClosure.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adjoining an executable frontier preserves predecessor closure.",
        H("Frontier Extension Closure"),
        Blocks(Describe.Lean(
            DescribeId.Create("frontier-union-preserves-predecessor-closure"),
            DeclarationHandle.Create(Prefix + "predecessorClosed_union_frontier"),
            H("Adding the whole frontier preserves predecessor closure"),
            StatementSource.FromAuthor(ClosureFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Fix completed and pending sets. If the completed set is closed under direct "
                        + "prerequisites, adjoining every node ready over that set preserves the "
                        + "same closure property.")),
                Paragraph(Text(
                    "A prerequisite of an old completed node is supplied by the closure "
                        + "hypothesis; "
                        + "a prerequisite of a frontier node is already completed by readiness."))),
            DescribeRole.Theorem))));

    private static Formula ClosureFormula()
    {
        Formula edge = F.Id("edge");
        Formula completed = F.Id("completed");
        Formula pending = F.Id("pending");

        return Disp(Seq(
            Forall, Sp, edge, Colon, Sp,
            F.Id("V"), Sp, To, Sp, F.Id("V"), Sp, To, Sp, F.Id("Prop"), Comma, Sp,
            completed, Comma, Sp, pending, Colon, Sp, Call("Set", F.Id("V")),
            Comma, RowBreak, Grp(),
            Call("PredecessorClosed", edge, completed), Sp, Rightarrow, RowBreak, Grp(),
            Call("PredecessorClosed", edge,
                Call("union", completed,
                    Call("executableFrontier", edge, completed, pending))), Dot));
    }
}
