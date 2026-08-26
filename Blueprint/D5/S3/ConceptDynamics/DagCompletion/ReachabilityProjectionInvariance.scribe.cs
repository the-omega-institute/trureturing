using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DagCompletion;

internal sealed class ReachabilityProjectionInvarianceDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DagCompletion/ReachabilityProjectionInvariance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prerequisite and consequence closures depend only on reachability, not the chosen "
            + "direct-edge presentation.",
        H("Reachability Projection Invariance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("same-reachability-gives-same-prerequisite-closure"),
                DeclarationHandle.Create(Prefix + "prerequisiteClosure_eq"),
                H("Reachability-equivalent graphs have equal prerequisite closures"),
                StatementSource.FromAuthor(ClosureFormula("prerequisiteClosure", "targets")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "If two direct-edge relations induce the same reflexive-transitive "
                            + "reachability relation, they generate identical prerequisite "
                            + "closures "
                            + "of every displayed target set.")),
                    Paragraph(Text(
                        "The SameReachability hypothesis is explicit; equality of direct edge "
                            + "relations is neither assumed nor concluded."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("same-reachability-gives-same-consequence-closure"),
                DeclarationHandle.Create(Prefix + "consequenceClosure_eq"),
                H("Reachability-equivalent graphs have equal consequence closures"),
                StatementSource.FromAuthor(ClosureFormula("consequenceClosure", "sources")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For the same pair of reachability-equivalent presentations, consequence "
                            + "closures of a displayed source set are equal.")),
                    Paragraph(Text(
                        "The theorem changes only the edge presentation and holds the source set "
                            + "fixed on both sides."))),
                DescribeRole.Theorem))));

    private static Formula ClosureFormula(string closure, string setName)
    {
        Formula first = F.Id("firstEdge");
        Formula second = F.Id("secondEdge");
        Formula set = F.Id(setName);

        return Disp(Seq(
            Forall, Sp, first, Comma, Sp, second, Colon, Sp,
            F.Id("V"), Sp, To, Sp, F.Id("V"), Sp, To, Sp, F.Id("Prop"),
            Comma, Sp, set, Colon, Sp, Call("Set", F.Id("V")),
            Comma, RowBreak, Grp(),
            Call("SameReachability", first, second), Sp, Rightarrow, RowBreak, Grp(),
            Call(closure, first, set), Sp, Eq, Sp, Call(closure, second, set), Dot));
    }
}
