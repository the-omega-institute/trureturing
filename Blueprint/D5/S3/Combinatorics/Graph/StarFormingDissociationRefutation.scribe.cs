using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class StarFormingDissociationRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A bipartite graph on ten vertices has a minimal two-star-forming set of size six, "
            + "but every two-independent set has size at most five.",
        H("Two-independence and upper two-star formation differ"),
        Blocks(
            Paragraph(Text("Let G be a finite simple graph on V, with decidable adjacency. "
                + "Write d(G,S,v) for the number of neighbours of v in S. All sets below "
                + "are finite vertex sets. The definitions are those of Rafik Sahbi, "
                + "Upper k-Star-Forming Sets, k-Independence, and Upper Domination, "
                + "arXiv:2610.03785v2, Definition 2.1 and Conjecture 4.2.")),
            Describe.Lean(DescribeId.Create("h0-reusable-properties"),
                DeclarationHandle.Create(Prefix + "h0_properties"), H("The original H0 certificate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original ten-vertex graph is two-colorable, its selected "
                    + "six-set is inclusion-minimal two-star-forming, and beta two is at most five. "
                    + "These are the same proof bodies consumed by result, exposed for arbitrary "
                    + "port compositions. The public edges, counterGraph and selected definitions "
                    + "retain the original vertex labels, neighborhoods and selected set."))), DescribeRole.Theorem),
            Node("claim", "Equality on all bipartite finite graphs", ClaimFormula(),
                "Conjecture 4.2 asserts equality for every bipartite finite graph. "
                    + "Graphs on Fin n cover every finite simple graph up to isomorphism. "
                    + "Bipartiteness is expressed by a proper colouring with two colours.",
                DescribeRole.Definition),
            Node("result", "The equality is false", Disp(new Formula.Not(F.Id("claim"))),
                "Use vertices 0 through 9, with sides 0 through 4 and 5 through 9. "
                    + "The neighbourhoods on the first side are {5,6,9}, {5,6,8}, "
                    + "{8,9}, {6,7,8,9}, and {5,7,8,9}, respectively. Colour by side. "
                    + "The set {0,1,2,5,6,7} satisfies the local criterion, while each "
                    + "of its 63 proper subsets fails it. It is therefore minimal "
                    + "two-star-forming, so SF is at least six. Each of the 210 "
                    + "six-element vertex sets contains a vertex with at least two "
                    + "selected neighbours. Any larger two-independent set would "
                    + "contain a two-independent six-element subset, since deletion "
                    + "cannot increase selected degrees. Thus beta is at most five "
                    + "and the asserted equality fails.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("sahbi-2026-star-forming-bipartite-refutation"),
                    ResolutionKind.Refuted)))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);

    private static Formula ClaimFormula()
    {
        var n = F.Id("n"); var graph = F.Id("G");
        return Disp(Iff(F.Id("claim"), All("n", F.Id("Nat"),
            All("G", Call("SimpleGraph", Call("Fin", n)),
                Imp(Call("Colorable", graph, D(2)),
                    Eq(Call("beta", graph, D(2)), Call("SF", graph, D(2))))))));
    }

    private static DocumentBlock Node(string selector, string title, Formula formula,
        string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(selector == "starForming_two_iff"
                ? "sf2-star-forming-two-iff" : "sf2-" + selector.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + selector), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
