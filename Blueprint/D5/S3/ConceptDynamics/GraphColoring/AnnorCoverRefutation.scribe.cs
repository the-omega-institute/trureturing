using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GraphColoring.GraphDominationFormula;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GraphColoring;

internal sealed class AnnorCoverRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/GraphColoring/AnnorCoverRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/annor2025domination");
    private static readonly LibraryNoteRef Prior = LibraryNoteRef.Create("D5/L/vemuri2019domination");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "No universal positive constant bounds cover domination below by fold times base domination.",
        H("Refutation of Annor Conjecture 14"), Blocks(
            Paragraph(Text("The source asserts the existence of a universal positive constant. "
                + "The following refutation is repository work, with novelty suspected only after "
                + "a bounded literature check. It requires independent review. Known product-graph "
                + "and perfect-code ingredients are not counted as separate results.")),
            Entry("every-constant-fails", "exists_cover_violation", "A strict violation for every constant", Violation()),
            Entry("conjecture-fourteen-false", "annor_conjecture14_false", "No universal constant", Negation()),
            Paragraph(Text("Vertex(r,m) is the function type Fin(r+1) to Fin(m+1). "
                + "Two vertices are adjacent exactly when they differ in every coordinate. "
                + "The product is categorical, not Cartesian. Its domination theory is established "
                + "in the cited literature; these elementary ingredients are not claimed novel.")),
            ProductEntry("product-regular", "productGraph_regular", "Degree", Regular()),
            ProductEntry("product-connected", "productGraph_connected", "Connectedness", Connected()),
            ProductEntry("product-domination-lower", "productGraph_domination_lower", "Domination lower bound", Lower()),
            ProductEntry("product-density", "productGraph_density", "Uniform density", Density()))));
    private static DocumentBlock Entry(string id, string declaration, string title, Formula formula) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula),
            AssessedProvenance.NovelAfterSearch(GidRef.Create("D5/L/annor2025domination"), Source),
            Blocks(Paragraph(Text("V and W range over finite types, and F and G are undirected simple graphs. "
                + "IsCover means an onto map, a bijection on each open neighborhood, and fiber cardinality k. "
                + "Domination numbers and k are coerced from naturals to reals in the inequality. "
                + "The witnesses have connected bases and positive folds; the source does not require G "
                + "connected. With t=r+1, the base has order (2t+1)^t, degree (2t)^t and domination at least t. "
                + "The cover domination is at most the base order. Bernoulli gives base order at most twice its degree. "
                + "Choosing r greater than 2/c makes the violation strict for any positive c."))), DescribeRole.Theorem);
    private static Formula Variables(Formula quantifier) => Seq(quantifier, Sp,
        Typed(F.Id("V"), Type()), Comma, Typed(F.Id("W"), Type()), Comma,
        Typed(F.Id("fv"), Call("Fintype", F.Id("V"))), Comma,
        Typed(F.Id("fw"), Call("Fintype", F.Id("W"))), Comma, RowBreak, Grp(),
        Typed(F.Id("F"), Call("SimpleGraph", F.Id("V"))), Comma,
        Typed(F.Id("G"), Call("SimpleGraph", F.Id("W"))), Comma,
        Typed(F.Id("p"), Seq(F.Id("W"), Sp, To, Sp, F.Id("V"))), Comma, Typed(F.Id("k"), Nat()), Comma, RowBreak, Grp());
    private static Formula Cover() => Call("IsCover", F.Id("G"), F.Id("F"), F.Id("p"), F.Id("k"));
    private static Formula Bound() => Seq(F.Id("c"), Sp, Cdot, Sp, F.Id("k"), Sp, Cdot, Sp, Gamma(F.Id("F")));
    private static Formula Positive(Formula x) => Seq(D(0), Lt, x);
    private static Formula Violation() => Display(Seq(Forall, Sp, Typed(F.Id("c"), Real()), Comma,
        Positive(F.Id("c")), Sp, Rightarrow, Sp, RowBreak, Grp(), Variables(Exists),
        And(Call("Connected", F.Id("F")), Positive(F.Id("k")), Cover(), Seq(Gamma(F.Id("G")), Lt, Bound()))));
    private static Formula Negation() => Display(Seq(Neg, Open, Exists, Sp, Typed(F.Id("c"), Real()), Comma,
        And(Positive(F.Id("c")), Seq(Variables(Forall), Positive(F.Id("k")), Sp, Rightarrow, Sp, Cover(), Sp, Rightarrow, Sp,
            Bound(), Sp, Le, Sp, Gamma(F.Id("G")))), Close));

    private static DocumentBlock ProductEntry(string id, string declaration, string title, Formula formula) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(Prior),
            Blocks(Paragraph(Text("The proof uses finite coordinate choices and cardinalities. "
                + "For domination, assign one distinct coordinate to each selected vertex and use "
                + "an unused coordinate to stay outside the selected set. For density, apply "
                + "Bernoulli's inequality to one minus the reciprocal of 2(r+1)+1."))), DescribeRole.Theorem);
    private static Formula Graph() => Call("productGraph", F.Id("r"), F.Id("m"));
    private static Formula PrefixRM() => Seq(Forall, Sp, Typed(F.Id("r"), Nat()), Comma, Typed(F.Id("m"), Nat()), Comma);
    private static Formula Regular() => Display(Seq(PrefixRM(), Call("IsRegularOfDegree", Graph(), Sup(F.Id("m"), PlusOne(F.Id("r"))))));
    private static Formula Connected() => Display(Seq(PrefixRM(), D(2), Sp, Le, Sp, F.Id("m"), Sp, Rightarrow, Sp, Call("Connected", Graph())));
    private static Formula Lower() => Display(Seq(PrefixRM(), F.Id("r"), Sp, Le, Sp, F.Id("m"), Sp, Rightarrow, Sp, PlusOne(F.Id("r")), Sp, Le, Sp, Gamma(Graph())));
    private static Formula Density()
    {
        Formula n = PlusOne(F.Id("r")), twice = Seq(Open, D(2), Sp, Cdot, Sp, n, Close);
        return Display(Seq(Forall, Sp, Typed(F.Id("r"), Nat()), Comma,
            Sup(PlusOne(twice), n), Sp, Le, Sp, D(2), Sp, Cdot, Sp, Sup(twice, n)));
    }
}
