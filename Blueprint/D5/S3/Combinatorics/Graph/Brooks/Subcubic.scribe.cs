using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Brooks;

internal sealed class SubcubicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite simple graph with maximum degree at most three and no four-clique admits a proper three-coloring.",
        H("Subcubic Brooks Theorem"),
        Blocks(
            Paragraph(Text(
                "Juan Pablo Traverso Gianini's formalization proves the subcubic case of Brooks' theorem. "
                + "The graph may be "
                + "disconnected and its vertex type may be empty. FiniteSimpleGraphs below "
                + "means a simple graph on a finite enumerated vertex type with decidable "
                + "adjacency. MaxDegree is the maximum vertex degree; CliqueFree(G,4) excludes "
                + "a set of four pairwise adjacent vertices. Colorable(G,3) means existence "
                + "of a map from vertices to three colors that separates adjacent vertices.")),
            Describe.Lean(DescribeId.Create("subcubic-brooks"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Brooks/Subcubic.brooks_cubic"),
                H("Three Colors for Subcubic Graphs"),
                StatementSource.FromAuthor(Disp(All("G", Call("FiniteSimpleGraphs"),
                    Implies(And(LessEqual(Call("MaxDegree", F.Id("G")), D(3)),
                        Call("CliqueFree", F.Id("G"), D(4))),
                        Call("Colorable", F.Id("G"), D(3)))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/GraphInvariants/traversogianini2026brooks")),
                Blocks(Paragraph(Text(
                    "The proof colors each connected component. A component with a vertex "
                    + "of degree below three uses a greedy ordering. A cubic component uses "
                    + "the good-triple construction or a cut partition and compatible color "
                    + "gluing. The hereditary density application is proved separately; an "
                    + "average degree bound alone is not this theorem's hypothesis.")),
                    Paragraph(Text(
                        "The cited source contains the formal proof; its helper lemmas organize "
                        + "the greedy ordering, separating vertices, endblocks and color gluing. "
                        + "Brooks' classical theorem supplies the mathematical precedent."))),
                DescribeRole.Theorem))));

    private static Formula LessEqual(Formula l, Formula r) => Seq(l, Sp, Leq, Sp, r);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula And(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.And, r);
    private static Formula Implies(Formula l, Formula r) =>
        new Formula.Logic(Seq(Open, l, Close), FormulaLogicOperator.Implies, Seq(Open, r, Close));
}
