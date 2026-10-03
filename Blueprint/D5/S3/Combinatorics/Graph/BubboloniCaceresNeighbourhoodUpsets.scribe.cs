using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class BubboloniCaceresNeighbourhoodUpsetsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/BubboloniCaceresNeighbourhoodUpsets.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/bubbolonicaceres2026neighbourhood");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let V be any finite nonempty vertex set and G any simple undirected graph on V. Closed neighbourhoods include their centre. No connectivity, absence of universal vertices, or distinction of equal neighbourhoods is assumed.",
        H("Upsets in neighbourhood convex geometries"),
        Blocks(
            Definition("closed-neighbourhood", "closedNeighbourhood", "Closed neighbourhood",
                "B(x) consists of x and every vertex adjacent to x in G."),
            Definition("common", "common", "Neighbourhood polarity",
                "N(X) is the intersection of B(x) over x in X. In particular N(empty) is V. Symmetry makes N antitone and gives X contained in N(N(X)) and N(N(N(X))) = N(X)."),
            Definition("convex", "convex", "Neighbourhood-convex sets",
                "The family C is the image of N together with the empty set: K belongs to C exactly when K is empty or K = N(Y) for some subset Y of V."),
            Definition("hull", "hull", "Empty-preserving hull",
                "h(empty) is empty, and h(X) = N(N(X)) for every nonempty X. Double polarity at the empty set is not identified with this empty-preserving hull."),
            Definition("extremes", "extremes", "Extreme points by deletion",
                "ex(K) consists of those x in K for which deleting x from K leaves a member of C."),
            Describe.Lean(
                DescribeId.Create("neighbourhood-upsets-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Every upset is neighbourhood-convex"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every finite nonempty V, every simple undirected G on V and every subset U of V, assume h(ex(K)) = K for every K in C. If x in U and B(x) contained in B(y) always imply y in U, then U belongs to C, including when U is empty. On the image L of N, polarity is an order-reversing involution with bottom S = N(V). Extreme-point generation supplies a deletable point outside each proper closed subset. Deletion induction, with covers transported by polarity, proves card(K) + card(N(K)) = card(V) + card(S) for K in L. Inclusion-exclusion then forces actual union closure in L and hence in C. Lemma 29(iii) identifies each principal upset with N(N({x})); finite unions of these principal upsets give U. The rank identity is not asserted for the extra empty set when it lies outside L."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bubboloni-caceres-neighbourhood-upsets"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Definition(string id, string declaration, string title, string prose) =>
        Describe.Lean(
            DescribeId.Create("neighbourhood-upsets-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula ResultFormula() => Disp(All("V", F.Id("FiniteNonemptySets"),
        All("G", Call("SimpleGraphs", F.Id("V")),
        All("U", Call("PowerSet", F.Id("V")),
        Implies(
            All("K", F.Id("C"), Equal(Call("h", Call("ex", F.Id("K"))), F.Id("K"))),
            Implies(
                All("x", F.Id("U"), All("y", F.Id("V"),
                    Implies(SubsetOf(Call("B", F.Id("x")), Call("B", F.Id("y"))),
                        Member(F.Id("y"), F.Id("U"))))),
                Member(F.Id("U"), F.Id("C"))))))));

    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(variable), domain, body);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula SubsetOf(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.SubsetOf, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.Implies, Seq(Open, right, Close));
}
