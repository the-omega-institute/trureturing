using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StoneCech;

internal sealed class DeletedSquareChromaticDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Topology/StoneCech/DeletedSquareChromatic.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Topology/feldmanwilce2026compactnesscliques");
    private static Formula V(string name) => F.Id(name);
    private static Formula App(string name, params Formula[] args) => Call(name, args);
    private static Formula And(Formula a, Formula b) => Seq(Grp(a), Sp, Land, Sp, Grp(b));
    private static Formula Not(Formula a) => Seq(Neg, Grp(a));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Imp(Formula a, Formula b) => Seq(Grp(a), Sp, Rightarrow, Sp, b);
    private static Formula Iff(Formula a, Formula b) => Seq(Grp(a), Sp, Leftrightarrow, Sp, Grp(b));
    private static Formula Fn(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Inst(string name, Formula type, Formula body) =>
        Seq(OpenBracket, App(name, type), CloseBracket, Comma, Sp, body);
    private static Formula WithType(string name, Formula body) =>
        All("u", V("UniverseLevel"), All(name, Seq(V("Type"), Underscore, Grp(V("u"))),
            body));
    private static Formula WithSpace(string name, Formula body) =>
        WithType(name, Inst("TopologicalSpace", V(name), body));
    private static Formula X => App("DeletedSquare", App("Ultrafilter", V("Nat")));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The deleted square of beta Nat has bounded cliques for every closed orthogonality, but its swap graph admits no finite open independent cover.",
        H("Bounded cliques without finite open chromatic number"),
        Blocks(
            Describe.Lean(DescribeId.Create("deleted-square-space"),
                DeclarationHandle.Create(Prefix + "DeletedSquare"), H("The actual deleted square"),
                StatementSource.FromAuthor(Disp(WithType("K", Seq(App("DeletedSquare", V("K")), Sp, Eq, Sp,
                    OpenBrace, V("z"), Colon, Sp, V("K"), Sp, Times, Sp, V("K"), Sp, Mid, Sp,
                    App("fst", V("z")), Sp, Neq, Sp, App("snd", V("z")), CloseBrace)))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "DeletedSquare K is the subtype of ordered unequal pairs in K times K, with exactly the induced product topology. It inherits Hausdorffness when K is Hausdorff. For the endpoint K is the compact Stone space of all ultrafilters on Nat, homeomorphic to the Stone–Cech compactification of discrete Nat."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("deleted-square-bounded-property"),
                DeclarationHandle.Create(Prefix + "BoundedCliqueProperty"), H("Universal bounded-clique property"),
                StatementSource.FromAuthor(Disp(WithSpace("X", Iff(App("BoundedCliqueProperty", V("X")),
                    All("G", App("SimpleGraph", V("X")),
                    Imp(App("IsClosed", App("AdjSet", V("G"))),
                        Seq(Exists, Sp, V("N"), Colon, Sp, V("Nat"), Comma, Sp,
                            All("S", App("Set", V("X")), Imp(App("IsClique", V("G"), V("S")),
                                And(App("Finite", V("S")), Seq(App("ncard", V("S")), Sp, Le, Sp, V("N")))))))))))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "A SimpleGraph is exactly an arbitrary symmetric irreflexive binary relation. AdjSet G is the set of all pairs (x,y) with G.Adj x y, in the entire product X times X, including its diagonal. Every subset S whose distinct pairs are related is quantified over. The conclusion requires finiteness as well as the ncard bound; it does not use ncard's zero value on infinite sets to hide infinite cliques. The bound may depend on G."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("deleted-square-open-property"),
                DeclarationHandle.Create(Prefix + "FiniteOpenChromaticProperty"), H("Universal finite open chromatic property"),
                StatementSource.FromAuthor(Disp(WithSpace("X", Iff(App("FiniteOpenChromaticProperty", V("X")),
                    All("G", App("SimpleGraph", V("X")),
                    Imp(App("IsClosed", App("AdjSet", V("G"))),
                        Seq(Exists, Sp, V("m"), Colon, Sp, V("Nat"), Comma, Sp,
                            Exists, Sp, V("U"), Colon, Sp, Fn(App("Fin", V("m")), App("Set", V("X"))),
                            Comma, Sp, App("OpenIndependentCover", V("G"), V("U"))))))))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "OpenIndependentCover G U means every U(i) is open, every point lies in at least one U(i), and for every i no two points in U(i) are adjacent. There is no partition or disjointness requirement. Both zero and one proposed colors remain in the quantifier m : Nat. The property again quantifies over every whole-product closed symmetric irreflexive relation."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("deleted-square-swap-graph"),
                DeclarationHandle.Create(Prefix + "swapGraph"), H("The coordinate-swap orthogonality"),
                StatementSource.FromAuthor(Disp(WithType("K",
                    All("x", App("DeletedSquare", V("K")), All("y", App("DeletedSquare", V("K")), Seq(
                    App("Adj", App("swapGraph", V("K")), V("x"), V("y")), Sp, Leftrightarrow, Sp,
                    And(Seq(App("fst", V("x")), Sp, Eq, Sp, App("snd", V("y"))),
                        Seq(App("snd", V("x")), Sp, Eq, Sp, App("fst", V("y")))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For every type K this is a SimpleGraph on DeletedSquare K. Symmetry reverses the two equalities, and a self-edge would equate the two coordinates of a deleted-square point. When K is Hausdorff, the two equality sets are closed in the entire product of the deleted square with itself."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("deleted-square-power"),
                DeclarationHandle.Create(Prefix + "countablyCompactSpace_deletedSquare_power"),
                H("Countable compactness of the full countable power"),
                StatementSource.FromAuthor(Disp(WithSpace("K",
                    Inst("CompactSpace", V("K"), Inst("T2Space", V("K"),
                        Inst("ExtremallyDisconnected", V("K"),
                            App("CountablyCompactSpace", Fn(V("Nat"), App("DeletedSquare", V("K")))))))))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The theorem applies to arbitrary compact Hausdorff extremally disconnected K, with its given topology. Countable compactness is the native countable-open-cover property, equivalently that every sequence has a cluster point. Neither sequential compactness nor a general product theorem for countably compact spaces is used.")),
                    Paragraph(Text("On each infinite pool, enumerate the pool increasingly and apply the native PointPairSeparation eventual-equality theorem contrapositively. If no clopen separates infinitely many pairs in either orientation, each fixed clopen test eventually agrees, forcing eventual equality and contradicting the deleted-square condition. Complementation turns this into an oriented clopen separator. Repeat for each coordinate, retaining decreasing infinite pools. The native diagonal_pool supplies an infinite pseudointersection; injective enumeration makes the exceptional preimage finite for every coordinate.")),
                    Paragraph(Text("Embed the countable power of DeletedSquare K into the compact ambient product Nat to K times K by taking subtype values coordinatewise. A cluster point of the thinned sequence belongs to every fixed closed rectangle C(j) times complement(C(j)), because the corresponding tail lies there. Thus every coordinate stays off the diagonal. The inducing product embedding transfers the cluster point back to the deleted-square power, and the cofinal increasing subsequence transfers it to the original sequence."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("deleted-square-power-cliques"),
                DeclarationHandle.Create(Prefix + "boundedCliqueProperty_of_countablyCompact_power"),
                H("The countable-power criterion for all closed orthogonalities"),
                StatementSource.FromAuthor(Disp(WithSpace("X",
                    Inst("CountablyCompactSpace", Fn(V("Nat"), V("X")),
                        App("BoundedCliqueProperty", V("X")))))),
                AssessedProvenance.FromLiterature(Source), Blocks(
                    Paragraph(Text("This is Feldman–Wilce Theorem 1, formalized independently from the mathematical argument. Constant-coordinate sequences transfer the power cluster property to X. An infinite clique sequence has a cluster point x; every neighborhood rectangle of (x,x) contains two terms of distinct indices. Closedness then gives a loop, a contradiction. This excludes every infinite clique subset by a choice of an injective natural-number sequence in it.")),
                    Paragraph(Text("If finite clique sizes had no uniform bound, choose an (n+1)-point clique for each n, enumerate its entries in the first n+1 coordinates, and pad with its last entry. A cluster point q of this sequence in Nat to X satisfies adjacency between q(i) and q(j) for all distinct i and j: the corresponding pairs lie eventually in the closed adjacency set. Applying the previous cluster-point contradiction to q gives the uniform bound. No closedness restriction away from the diagonal or separation axiom is added to this criterion."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("deleted-square-ramsey-obstruction"),
                DeclarationHandle.Create(Prefix + "no_finite_open_independent_cover"),
                H("The swap graph excludes every finite open independent cover"),
                StatementSource.FromAuthor(Disp(All("m", V("Nat"),
                    All("U", Fn(App("Fin", V("m")), App("Set", X)),
                        Not(App("OpenIndependentCover", App("swapGraph", App("Ultrafilter", V("Nat"))), V("U"))))))),
                AssessedProvenance.FromRepo(Source), Blocks(
                    Paragraph(Text("The swap graph relates (p,q) to (r,s) exactly when p=s and q=r. These two equality conditions make its adjacency set closed in the whole product. Swapping is symmetric, and deleting the diagonal makes the graph irreflexive.")),
                    Paragraph(Text("For distinct natural principal points a,b, record every color containing (a,b). Color an unordered pair a<b by the ordered pair of its two full membership patterns. Reuse Yann Pequignot's Apache-2.0 relativized infinite Ramsey theorem from NathansonProblem9, with its original proof and attribution intact. It yields an infinite A and fixed directional patterns P,Q. Independence makes P and Q disjoint.")),
                    Paragraph(Text("Split A into disjoint infinite supports A0,A1 with the native split_pool. Extend cofinite intersect principal(Ai) to free ultrafilters p,q. The supports force p distinct from q. A cover member containing (p,q) contains a relative basic clopen rectangle. Intersect the rectangle's supports with A0,A1. Freeness makes both resulting supports infinite and hence unbounded in Nat. One principal pair in the rectangle has increasing order; another has decreasing order. Homogeneity puts the same color in P and Q, a contradiction. These two pairs need not be swaps. Full patterns retain the exact argument for overlapping covers."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("feldman-wilce-question-two-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Strictness of the second implication"),
                StatementSource.FromAuthor(Disp(And(App("T2Space", X),
                    And(App("BoundedCliqueProperty", X), Not(App("FiniteOpenChromaticProperty", X)))))),
                AssessedProvenance.FromRepo(Source), Blocks(
                    Paragraph(Text("Feldman–Wilce Section 5 Question 2 asks whether the second implication in compact implies finite open chromatic implies bounded cliques is strict. Here X is exactly DeletedSquare (Ultrafilter Nat). Mathlib projectivity of the Stone–Cech compactification of discrete Nat supplies extremal disconnectedness, transported by the existing native ultrafilter homeomorphism. The generic deleted-square power theorem and the countable-power criterion give bounded cliques for every closed orthogonality. The explicit swap graph refutes finite open chromatic number. Hausdorffness is inherited from the actual ambient product.")),
                    Paragraph(Text("The construction uses classical choice, with no CH, diamond, MA, metrizable-space restriction, common countable base, selector-existence premise, or original open assertion as a hypothesis. The source of the question and of the countable-power criterion is Feldman–Wilce. The deleted-square proof is supplied mathematical input assembled with native clopen separation and Ramsey reuse. No Lean implementation from the author repository is copied: its license is not granted. The primary-source status check is bounded and does not establish global priority or acceptance by the original authors.")),
                    Paragraph(Text("A conditional predecessor is Brandsma, van Hartskamp and van Mill, On colorings of topological groups, Topology Proceedings 22 (1997), 25–41, Example 2.3, https://staff.fnwi.uva.nl/j.vanmill/papers/papers1997/colorings.pdf. Under diamond, their first-countable countably compact Ostaszewski space has a fixed-point-free involution with no finite open coloring. First-countable countable compactness implies sequential compactness, so Feldman–Wilce Corollary 4(a) gives its bounded clique property. Its whole-product closed involution graph thus gives an older conditional separation. The inspected sources do not establish an earlier ZFC deleted-square solution."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("feldman-wilce-bounded-cliques-open-chromatic-strictness"),
                    ResolutionKind.Proved)))));
}
