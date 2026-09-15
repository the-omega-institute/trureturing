using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.GraphRepresentation;

internal sealed class ExplicitNonTwoUniformDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/GraphRepresentation/ExplicitNonTwoUniform.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/adamson2026twoword");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cuts in arbitrary words reconstruct their two-letter projections. The explicit "
        + "membership graph on 24 points and all their subsets has no two-uniform representation.",
        H("An Explicit Membership Graph Outside G₂"),
        Blocks(
            Paragraph(Text(
                "This construction addresses the unnumbered explicit-graph "
                + "request in the source conclusion. It does not address Conjecture 31, minimum "
                + "size or connectedness. The literature note attests the question and definitions, "
                + "not a published answer. Novelty is suspected only within the supplied "
                + "September 15, 2026 search scope; worldwide priority remains ASSUMED-UNVERIFIED.")),
            Paragraph(Text(
                "All words are finite lists. Projection and representation use decidable "
                + "equality on V; cuts need it only on B, reconstruction needs none, and the "
                + "reconstruction theorem assumes it on A and B. Sum(A,B) is the "
                + "tagged disjoint union, with injections inl and inr. Unit has the single "
                + "element *. Empty lists are written []. The left restriction L(w) is "
                + "filterMap(getLeft?,w), retaining each left letter in its original order. "
                + "The renaming rho(b) sends inl(a) to inl(a) and inr(*) to inr(b). "
                + "Its domain is Sum(A,Unit), and it is injective. Natural pred is truncated "
                + "subtraction by one. The displayed proj, cuts and Rec abbreviate twoProjection, "
                + "leftCuts and reconstruct. Finset(Fin(24)) is the full power set of the 24 points.")),
            Node("twoProjection", "The actual two-letter projection", ProjectionFormula(),
                "The filter keeps exactly the letters equal to either specified vertex, "
                + "preserving order and repetitions. This is the source projection, not an "
                + "alternation pattern or a union of graph representations.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("InG2", "Two words, each two-uniform", RepresentationFormula(),
                "Both occurrence conditions quantify over every vertex. Since two is positive, "
                + "both word alphabets equal the vertex type. The edge equivalence is required "
                + "for every distinct pair; SimpleGraph already excludes loops and is symmetric.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("leftCuts", "Cuts counted in the original word", CutsFormula(),
                "Each left letter increments every later cut. An occurrence of b contributes "
                + "a zero cut before the cuts of the remaining suffix, while other right letters "
                + "are deleted. Thus the list records, in occurrence order, the number of "
                + "preceding left letters at every b. Right letters between occurrences are "
                + "ignored. Consecutive b markers may have the same cut.", DescribeRole.Definition),
            Node("reconstruct", "Insert markers at absolute cuts", ReconstructionFormula(),
                "With no cuts, retain the left list. A zero cut inserts a marker without "
                + "consuming a left letter, so tied cuts give consecutive markers. A positive "
                + "cut consumes one left letter and decrements every remaining cut. The branch "
                + "with an empty left list and a positive first cut returns the empty list; "
                + "it is unreachable for cuts of actual words. Recursion decreases the sum "
                + "of the two input lengths.", DescribeRole.Definition),
            Node("projection_eq_reconstruction", "Reconstruction for every word",
                ReconstructionTheoremFormula(),
                "Induct on the original word. A left head shifts all cuts by one; the "
                + "reconstructor consumes that same head and restores the original cuts. "
                + "A right head equal to b inserts a zero cut and hence a marker. A different "
                + "right head changes neither side. Projecting and renaming gives the displayed "
                + "identity. There is no uniformity, cut-separation or word-order hypothesis."),
            Node("U24", "The literal membership graph", GraphFormula(),
                "The carrier is the tagged union V of Fin(24) and all finite subsets of Fin(24). "
                + "Adjacency is membership across the two tags, in either direction, and false "
                + "within either part. These equations directly provide symmetry and "
                + "looplessness. V is finite with 24 + 2^24 = 16,777,240 vertices. The vertex "
                + "inr(emptyset) is isolated and is permitted by the source definition.",
                DescribeRole.Definition),
            Node("u24_not_in_g2", "No pair of two-uniform words represents U₂₄",
                EndpointFormula(),
                "Assume the displayed representation. Each left restriction has length 48, "
                + "because each of the 24 left letters occurs twice. Each subset occurs twice, "
                + "so its cut list has length two, and every cut is between zero and 48. "
                + "Choose these two cuts in each word to obtain a signature in (Fin(49) × "
                + "Fin(49))². The domain has 2^24 = 16,777,216 elements, whereas the signature "
                + "space has 49^4 = 5,764,801. The existing pigeonhole theorem therefore gives "
                + "distinct subsets S,T with equal signatures. Apply reconstruction separately "
                + "to w and v for each left letter a. Injectivity of rho(S) and rho(T) shows "
                + "that equality of the two a/S projections is equivalent to equality of the "
                + "two a/T projections. Hence a belongs to S exactly when it belongs to T. "
                + "Finite-set extensionality gives S=T, contradicting distinctness. The two "
                + "left restrictions may have different orders throughout this proof."),
            Paragraph(Text("The pigeonhole step directly reuses "),
                Ref("D5/S0/Diagonal/PigeonholeFiber.finite_reading_has_fiber"),
                Text(". Count identities, finite cardinalities, marker injectivity and "
                    + "membership extensionality are local steps, not separate new theorems. "
                    + "The live new content in both theorem proofs is reconstruction from cuts. "
                    + "The argument is structural for arbitrary words; the concluding finite "
                    + "arithmetic does not enumerate words or graphs.")))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("u24-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);

    private static Formula X(string value) => F.Id(value);
    private static Formula Named(string value) => Seq(Operatorname, Grp(X(value)));
    private static Formula App(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, X(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula And(Formula first, Formula second) =>
        Seq(Par(first), Sp, Land, Sp, Par(second));
    private static Formula Eq(Formula first, Formula second) => Equal(first, second);
    private static Formula IffEq(Formula first, Formula second) =>
        Seq(Par(first), Sp, Iff, Sp, Par(second));
    private static Formula List(Formula type) => App("List", type);
    private static Formula Sum(Formula a, Formula b) => App("Sum", a, b);
    private static Formula Empty() => Seq(OpenBracket, CloseBracket);
    private static Formula Cons(Formula a, Formula w) => Seq(Par(a), Colon, Colon, w);
    private static Formula Inl(Formula a) => App("inl", a);
    private static Formula Inr(Formula b) => App("inr", b);
    private static Formula P(Formula a, Formula b, Formula w) => App("proj", a, b, w);
    private static Formula Cuts(Formula b, Formula w) => App("cuts", b, w);
    private static Formula Rec(Formula r, Formula cuts) => App("Rec", r, cuts);
    private static Formula Natural() => Seq(Mathbb, Grp(X("N")));
    private static Formula Map(Formula f, Formula w) => App("map", f, w);
    private static Formula Uniform(Formula w) =>
        All("z", X("V"), Eq(App("count", X("z"), w), D(2)));
    private static Formula Representation(Formula graph) =>
        And(Uniform(X("w")), And(Uniform(X("v")),
            All("x", X("V"), All("y", X("V"),
                Seq(X("x"), Sp, Neq, Sp, X("y"), Sp, Implies, Sp,
                    IffEq(App("Adj", graph, X("x"), X("y")),
                        Eq(P(X("x"), X("y"), X("w")),
                            P(X("x"), X("y"), X("v")))))))));
    private static Formula ExistsWords(Formula body) =>
        Seq(Exists, Sp, X("w"), Comma, X("v"), Colon, Sp, List(X("V")), Comma, Sp, body);
    private static Formula Equations(params Formula[] rows) =>
        Disp(Seq(Begin, Grp(X("gathered")),
            Seq(rows.SelectMany((row, index) => index == 0
                ? new[] { row } : new[] { RowBreak, row }).ToArray()),
            End, Grp(X("gathered"))));

    private static Formula ProjectionFormula() => Disp(
        All("V", Named("Type"), All("a", X("V"), All("b", X("V"),
            All("w", List(X("V")), Eq(P(X("a"), X("b"), X("w")),
                App("filter", Seq(X("z"), Mapsto, Par(Seq(X("z"), F.Eq, X("a"),
                    Sp, Lor, Sp, X("z"), F.Eq, X("b")))), X("w"))))))));

    private static Formula RepresentationFormula() => Disp(
        All("V", Named("Type"), All("G", App("SimpleGraph", X("V")),
            IffEq(App("InG2", X("G")), ExistsWords(Representation(X("G")))))));

    private static Formula CutsFormula() => Equations(
        Seq(Forall, Sp, X("A"), Comma, X("B"), Colon, Named("Type"), Comma, Sp,
            X("b"), Comma, X("c"), Colon, X("B"), Comma, Sp, X("a"), Colon, X("A"),
            Comma, Sp, X("w"), Colon, List(Sum(X("A"), X("B")))),
        Eq(Cuts(X("b"), Empty()), Empty()),
        Eq(Cuts(X("b"), Cons(Inl(X("a")), X("w"))),
            Map(Named("succ"), Cuts(X("b"), X("w")))),
        Eq(Cuts(X("b"), Cons(Inr(X("b")), X("w"))),
            Cons(D(0), Cuts(X("b"), X("w")))),
        Seq(X("c"), Sp, Neq, Sp, X("b"), Sp, Implies, Sp,
            Eq(Cuts(X("b"), Cons(Inr(X("c")), X("w"))), Cuts(X("b"), X("w")))));

    private static Formula ReconstructionFormula() => Equations(
        Seq(Forall, Sp, X("A"), Colon, Named("Type"), Comma, Sp, X("a"), Colon, X("A"),
            Comma, Sp, X("r"), Colon, List(X("A")), Comma, Sp, X("n"), Colon, Natural(),
            Comma, Sp, X("c"), Colon, List(Natural())),
        Eq(Rec(X("r"), Empty()), Map(Named("inl"), X("r"))),
        Eq(Rec(X("r"), Cons(D(0), X("c"))), Cons(Inr(Star), Rec(X("r"), X("c")))),
        Eq(Rec(Empty(), Cons(Add(X("n"), D(1)), X("c"))), Empty()),
        Eq(Rec(Cons(X("a"), X("r")), Cons(Add(X("n"), D(1)), X("c"))),
            Cons(Inl(X("a")), Rec(X("r"), Cons(X("n"), Map(Named("pred"), X("c")))))));

    private static Formula ReconstructionTheoremFormula() => Disp(
        All("A", Named("Type"), All("B", Named("Type"), All("a", X("A"),
            All("b", X("B"), All("w", List(Sum(X("A"), X("B"))),
                Eq(P(Inl(X("a")), Inr(X("b")), X("w")),
                    Map(App("rho", X("b")), P(Inl(X("a")), Inr(Star),
                        Rec(App("L", X("w")), Cuts(X("b"), X("w"))))))))))));

    private static Formula GraphFormula() => Equations(
        Eq(X("V"), Sum(App("Fin", D(2, 4)), App("Finset", App("Fin", D(2, 4))))),
        Seq(Named("U24"), Colon, App("SimpleGraph", X("V"))),
        Seq(Forall, Sp, X("a"), Comma, X("b"), Colon, App("Fin", D(2, 4)), Comma, Sp,
            X("S"), Comma, X("T"), Colon, App("Finset", App("Fin", D(2, 4)))),
        IffEq(App("Adj", Named("U24"), Inl(X("a")), Inr(X("S"))),
            Seq(X("a"), Sp, InMacro, Sp, X("S"))),
        IffEq(App("Adj", Named("U24"), Inr(X("S")), Inl(X("a"))),
            Seq(X("a"), Sp, InMacro, Sp, X("S"))),
        And(Seq(Neg, App("Adj", Named("U24"), Inl(X("a")), Inl(X("b")))),
            Seq(Neg, App("Adj", Named("U24"), Inr(X("S")), Inr(X("T"))))));

    private static Formula EndpointFormula() => Disp(
        Seq(Neg, ExistsWords(Representation(Named("U24")))));
}
