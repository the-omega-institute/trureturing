using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DagCompletion;

internal sealed class DependencyAggregateRecursionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DagCompletion/DependencyAggregateRecursion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Global prerequisite meet and join aggregates satisfy exact local predecessor recursion "
            + "laws.",
        H("Dependency Aggregate Recursion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prerequisite-join-local-recursion"),
                DeclarationHandle.Create(Prefix + "prerequisiteJoin_recursion"),
                H("Prerequisite joins satisfy local recursion"),
                StatementSource.FromAuthor(RecursionFormula("prerequisiteJoin", "join")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "In a complete lattice, the global join over a node's prerequisite cone "
                            + "equals its own label joined with the joins of every direct "
                            + "predecessor.")),
                    Paragraph(Text(
                        "The equality includes all direct predecessors through the displayed local "
                            + "aggregate; it does not assume finiteness or choose an "
                            + "enumeration."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prerequisite-meet-local-recursion"),
                DeclarationHandle.Create(Prefix + "prerequisiteMeet_recursion"),
                H("Prerequisite meets satisfy local recursion"),
                StatementSource.FromAuthor(RecursionFormula("prerequisiteMeet", "meet")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Dually, the global prerequisite meet equals the node label met with every "
                            + "direct predecessor's prerequisite meet.")),
                    Paragraph(Text(
                        "The complete-lattice assumption is an instance binder. No distributivity "
                            + "or finite-lattice hypothesis is added."))),
                DescribeRole.Theorem))));

    private static Formula RecursionFormula(string aggregate, string operation)
    {
        Formula edge = F.Id("edge");
        Formula label = F.Id("label");
        Formula node = F.Id("node");
        Formula predecessor = F.Id("predecessor");
        Formula dependency = F.Id("dependency");
        Formula indexedOperation = Seq(
            Operatorname, Grp(F.Id(operation == "join" ? "iSup" : "iInf")),
            Underscore, Grp(Seq(predecessor, Colon, Sp, F.Id("V"))), Sp,
            Operatorname, Grp(F.Id(operation == "join" ? "iSup" : "iInf")),
            Underscore, Grp(Seq(
                dependency, Colon, Sp, Call("edge", predecessor, node))), Sp,
            Call(aggregate, edge, label, predecessor));
        Formula local = Call(
            operation == "join" ? "sup" : "inf",
            Call("label", node), indexedOperation);

        return Disp(Seq(
            Forall, Sp, edge, Colon, Sp,
            F.Id("V"), Sp, To, Sp, F.Id("V"), Sp, To, Sp, F.Id("Prop"), Comma, Sp,
            label, Colon, Sp, F.Id("V"), Sp, To, Sp, F.Id("Label"), Comma, Sp,
            node, Colon, Sp, F.Id("V"), Comma, RowBreak, Grp(),
            OpenBracket, Call("CompleteLattice", F.Id("Label")), CloseBracket,
            Comma, RowBreak, Grp(),
            Call(aggregate, edge, label, node), Sp, Eq, Sp, local, Dot));
    }
}
