using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LinearForests;

internal sealed class TreePathCutsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/LinearForests/TreePathCuts.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The components left by a cut on one path of a tree form a path of components.",
        H("Path cuts in trees"),
        Blocks(
            Describe.Lean(DescribeId.Create("tree-spine-component-path"),
                DeclarationHandle.Create(Owner + "componentGraph_path"),
                H("The residual component graph is a path"),
                StatementSource.FromAuthor(ComponentPath()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("OnSpine(G,C) means that one simple walk of G contains every edge of C. "
                        + "Contract each connected component of G after deleting C. Adjacencies of the "
                        + "component graph are original cut edges between their components.")),
                    Paragraph(Text("Every cut edge separates its endpoints and is unique between its "
                        + "two residual components. Project the original walk by keeping the cut edges. "
                        + "Its projection is a trail in an acyclic component graph, so it is a simple walk. "
                        + "Connectedness and closure under adjacency imply that its support contains every "
                        + "component. For the empty cut the quotient has one vertex."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula For(string id, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(id), type, body);

    private static Formula ComponentPath()
    {
        Formula v = F.Id("V"), g = F.Id("G"), c = F.Id("C"), n = F.Id("n");
        var next = new Formula.Binary(n, FormulaBinaryOperator.Add, D(1));
        var iso = Call("GraphIso", Call("pathGraph", next), Call("componentGraph", g, c));
        var exists = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("n"), F.Id("Nat"),
            Call("Nonempty", iso));
        return Disp(For("V", F.Id("Type"), For("G", Call("SimpleGraph", v),
            For("C", Call("Set", Call("Sym2", v)), new Formula.Logic(
                Seq(Open, new Formula.Logic(Call("IsTree", g), FormulaLogicOperator.And, Call("OnSpine", g, c)), Close),
                FormulaLogicOperator.Implies, Seq(Open, exists, Close))))));
    }
}
