using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DagCompletion;

internal sealed class ConsequenceClosureDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DagCompletion/ConsequenceClosure.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reachability generates the least successor-closed consequence set, dual to prerequisite "
            + "closure.",
        H("Consequence Closure"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("consequence-closure-is-least"),
                DeclarationHandle.Create(Prefix + "consequenceClosure_least"),
                H("Consequence closure is the least successor-closed superset"),
                StatementSource.FromAuthor(LeastFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "If a set contains all sources and is closed under direct dependents, it "
                            + "contains every node reachable from a source.")),
                    Paragraph(Text(
                        "The two closure hypotheses are explicit antecedents, and the conclusion "
                            + "is exactly containment of the generated consequence closure."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prerequisites-meet-targets-through-consequences"),
                DeclarationHandle.Create(
                    Prefix + "mem_prerequisiteClosure_iff_consequence_inter"),
                H("Prerequisite membership is witnessed by a consequence intersection"),
                StatementSource.FromAuthor(DualityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A node is in the prerequisite closure of a target set exactly when its "
                            + "singleton consequence cone meets that target set.")),
                    Paragraph(Text(
                        "The equivalence uses the same reachability direction on both sides and "
                            + "does not assert equality of the two closure sets."))),
                DescribeRole.Theorem))));

    private static Formula LeastFormula()
    {
        Formula edge = F.Id("edge");
        Formula sources = F.Id("sources");
        Formula closed = F.Id("closed");
        Formula hypotheses = Seq(
            sources, Sp, Subseteq, Sp, closed, Sp, Land, Sp,
            Call("SuccessorClosed", edge, closed));

        return Disp(Seq(
            Forall, Sp, edge, Colon, Sp,
            F.Id("V"), Sp, To, Sp, F.Id("V"), Sp, To, Sp, F.Id("Prop"), Comma, Sp,
            sources, Comma, Sp, closed, Colon, Sp, Call("Set", F.Id("V")),
            Comma, RowBreak, Grp(), Open, hypotheses, Close, Sp, Rightarrow,
            RowBreak, Grp(),
            Call("consequenceClosure", edge, sources), Sp, Subseteq, Sp, closed, Dot));
    }

    private static Formula DualityFormula()
    {
        Formula edge = F.Id("edge");
        Formula targets = F.Id("targets");
        Formula node = F.Id("node");

        return Disp(Seq(
            Forall, Sp, edge, Colon, Sp,
            F.Id("V"), Sp, To, Sp, F.Id("V"), Sp, To, Sp, F.Id("Prop"), Comma, Sp,
            targets, Colon, Sp, Call("Set", F.Id("V")), Comma, Sp,
            node, Colon, Sp, F.Id("V"), Comma, RowBreak, Grp(),
            node, Sp, InMacro, Sp, Call("prerequisiteClosure", edge, targets),
            Sp, Iff, RowBreak, Grp(),
            Call("Nonempty", Call("inter",
                Call("consequenceClosure", edge, Call("singleton", node)), targets)), Dot));
    }
}
