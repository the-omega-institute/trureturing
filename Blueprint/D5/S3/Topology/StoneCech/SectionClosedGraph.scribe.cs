using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StoneCech;

internal sealed class SectionClosedGraphDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/StoneCech/SectionClosedGraph.";
    private static Formula V(string n) => FormulaDsl.Id(n);
    private static Formula All(string n, Formula t) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp);
    private static Formula Ex(string n, Formula t) => Seq(Exists, Sp, V(n), Colon, Sp, t, Comma, Sp);
    private static Formula Mem(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula And(params Formula[] terms) => Seq(terms.SelectMany((f, i) =>
        i == 0 ? new[] { Grp(f) } : new[] { Sp, Land, Sp, Grp(f) }).ToArray());
    private static Formula Imp(Formula a, Formula b) => Seq(Grp(a), Sp, Rightarrow, Sp, Grp(b));
    private static Formula UfA => Call("Ultrafilter", V("A"));
    private static Formula SetY => Call("Set", UfA);
    private static Formula X => Call("principalExtension", V("Y"));
    private static Formula SetX => Call("Set", X);
    private static Formula Common => Seq(All("A", V("Type")), All("B", V("Type")),
        All("q", Seq(V("A"), Sp, To, Sp, V("B"))));
    private static Formula Good => Seq(V("Y"), Sp, Subseteq, Sp, Call("SectionGood", V("q")));
    private static Formula Small => Seq(Call("Card", V("Y")), Sp, Le, Sp, V("c"));
    private static Formula Projective => Call("InjOn", Call("map", V("q")), V("Y"));
    private static Formula SelectorCompact => Call("IsCountablyCompact", V("Y"));
    private static Formula Fibre => Call("fibre", V("q"), V("b"));
    private static Formula FiniteFibres => Seq(All("b", V("B")), Call("Finite", Fibre));
    private static Formula Unbounded => Seq(All("n", V("Nat")), Ex("b", V("B")),
        V("n"), Sp, Le, Sp, Call("ncard", Fibre));
    private static Formula Density => Seq(All("S", Call("Set", V("A"))),
        Imp(And(Call("Infinite", V("S")), Call("InjOn", V("q"), V("S"))),
            Seq(Ex("u", UfA), And(Mem(V("u"), V("Y")), Mem(V("S"), V("u"))))));
    private static Formula Closed => Call("IsClosed", Call("AdjSet", V("q"), V("Y")));
    private static Formula Clique => Call("IsClique", Call("fibreGraph", V("q"), V("Y")), V("K"));
    private static Formula FiniteCliques => Seq(All("K", SetX), Imp(Clique, Call("Finite", V("K"))));
    private static Formula ExactCliques => Seq(All("n", V("Nat")), Ex("K", SetX), And(
        Call("Finite", V("K")), Clique, Seq(Call("ncard", V("K")), Sp, Eq, Sp, V("n"))));
    private static Formula ClosedStatement => Disp(Seq(Common, All("Y", SetY),
        Imp(And(Good, Projective), Closed)));
    private static Formula CompactStatement => Disp(Seq(Common, All("Y", SetY),
        Imp(And(Good, SelectorCompact, Density, FiniteFibres), Call("IsCountablyCompact", X))));
    private static Formula CliqueStatement => Disp(Seq(Common, All("Y", SetY), All("K", SetX),
        Imp(And(FiniteFibres, Clique), Call("Finite", V("K")))));
    private static Formula EndpointStatement => Disp(Seq(Common,
        Imp(And(Call("Countable", V("A")), FiniteFibres, Unbounded),
            Seq(Ex("Y", SetY), And(Good, Small, Projective, SelectorCompact, Density,
                Call("CountablyCompactSpace", X), Closed, FiniteCliques, ExactCliques)))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual principal extension of a section-dense selector carries a closed fibre graph with finite cliques of every size.",
        H("A closed graph on a countably compact principal extension"), Blocks(
            Paragraph(Text("For arbitrary types A and B in Type and q : A -> B, put X=principalExtension(Y)=range(pure : A -> Ultrafilter A) union Y, "
                + "with the topology inherited as a subspace of Ultrafilter A. This is an actual vertex subspace, hence Hausdorff by the inherited T2 instance. "
                + "The principalEmbedding sends a to pure(a) regarded as a vertex of X and is injective. "
                + "fibreGraph(q,Y) relates x and y precisely when there are distinct a,b in A with x.val=pure(a), y.val=pure(b), and q(a)=q(b). "
                + "It is symmetric and irreflexive by construction. Its adjacency is principal-only; when Y is section-good, "
                + "its vertices are free and receive no edges.")),
            Paragraph(Text("Formula notation is shared across the four statements: fibre(q,b) is q-inverse({b}); map(q) is Ultrafilter.map q; "
                + "SectionGood(q) means free and containing an actual injectivity set of q; Card is Cardinal.mk and c is the continuum. "
                + "AdjSet(q,Y) is exactly {p : X times X | (fibreGraph q Y).Adj p.1 p.2}, a subset of the entire product X squared. "
                + "IsClique is SimpleGraph.IsClique, Finite and Infinite are the set predicates, and ncard is Set.ncard. "
                + "IsCountablyCompact is the ambient set predicate, whereas CountablyCompactSpace is the native typeclass on the indicated subspace. "
                + "None of these statements asserts sequential compactness.")),
            Describe.Lean(DescribeId.Create("all-product-closed-fibre-adjacency"),
                DeclarationHandle.Create(Owner + "isClosed_fibreGraph_adj"), H("Closedness in the entire product, including the diagonal"),
                StatementSource.FromAuthor(ClosedStatement), AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Topology/feldmanwilce2026compactnesscliques")), Blocks(
                    Paragraph(Text("The only hypotheses are Y contained in SectionGood(q) and injectivity of Ultrafilter.map q on Y. "
                        + "No countability, finite fibres, density or countable compactness is needed. The proof constructs an open nonedge rectangle "
                        + "around every nonadjacent ordered pair, including every diagonal pair. Basic neighborhoods are {x : X | S in x.val}, "
                        + "the restrictions of ambient membership clopens.")),
                    Paragraph(Text("For two principal points use their singleton basic neighborhoods; nonadjacency excludes the only possible edge in that rectangle. "
                        + "For a mixed principal/selector pair, use the principal singleton and the complement of its whole q-fibre at the selector point. "
                        + "That complement belongs to every section-good ultrafilter: its section witness meets the fibre in at most one point, "
                        + "and freeness rules out that finite intersection. The reversed mixed case is handled symmetrically.")),
                    Paragraph(Text("For equal selector values choose an actual section S in that ultrafilter and use its basic neighborhood squared. "
                        + "Two distinct principal points in S cannot share a q-value, so this square is edge-free. This is the necessary diagonal argument. "
                        + "For unequal selector values, projection injectivity makes their projected ultrafilters distinct. "
                        + "Choose T contained in B with T in one projection and its complement in the other. "
                        + "The basic neighborhoods of q-inverse(T) and q-inverse(complement T) form an edge-free rectangle. "
                        + "Thus the source addresses full-product closedness rather than only closedness away from the diagonal."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("countably-compact-principal-extension"),
                DeclarationHandle.Create(Owner + "isCountablyCompact_principalExtension"), H("Countable compactness from finite fibres and section density"),
                StatementSource.FromAuthor(CompactStatement), AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Topology/feldmanwilce2026compactnesscliques")), Blocks(
                    Paragraph(Text("Assume Y is section-good and countably compact, every infinite injectivity set S of q belongs to some u in Y, "
                        + "and every q-fibre is finite. Then the actual principal extension is countably compact as a subset of Ultrafilter A. "
                        + "This theorem does not assume a countable A or B, a bound on Card(Y), or projection injectivity.")),
                    Paragraph(Text("For an infinite subset C of the extension, if C intersect Y is infinite, countable compactness of Y supplies its AccPt in Y. "
                        + "Otherwise C has infinitely many principal points. Let P be their preimage in A. Finite fibres force q(P) to be infinite, "
                        + "since the preimage of a finite image would be a finite union of finite fibres. "
                        + "Choose a subset S of P on which q is injective with q(S)=q(P); it is infinite. "
                        + "Section density gives u in Y containing S. Principal ultrafilters converge to u along u itself; "
                        + "freeness makes u different from every principal point, giving a genuine punctured AccPt of pure(S), hence of C. "
                        + "The native T1 infinite-subset characterization gives IsCountablyCompact, without producing a convergent subsequence."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-cliques-in-finite-fibres"),
                DeclarationHandle.Create(Owner + "fibreGraph_clique_finite"), H("Every clique is finite"),
                StatementSource.FromAuthor(CliqueStatement), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For arbitrary Y, finite q-fibres alone imply that every clique K of fibreGraph(q,Y) is finite. "
                        + "An empty clique is finite. A singleton clique is finite even when its sole vertex is a selector point; "
                        + "the proof handles both through the subsingleton case. Otherwise choose two distinct members. Their edge makes the first "
                        + "a principal point pure(a). Every other member is either that vertex or is adjacent to it, hence principal and in the same q-fibre. "
                        + "Thus the whole clique lies in the image under principalEmbedding of the finite fibre over q(a). "
                        + "No goodness, projection injectivity, topology or countability assumption on Y is used."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("countably-compact-closed-fibre-graph"),
                DeclarationHandle.Create(Owner + "exists_countablyCompact_closed_fibreGraph"),
                H("Constructing the selector, space and finite unbounded cliques"), StatementSource.FromAuthor(EndpointStatement),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Topology/feldmanwilce2026compactnesscliques"),
                    LibraryNoteRef.Create("D5/L/Topology/frolik1960countablycompact"),
                    LibraryNoteRef.Create("D5/L/Topology/ginsburgsaks1975ultrafilters")), Blocks(
                    Paragraph(Text("Assume Countable A, all q-fibres finite, and for every natural n a fibre with n <= its ncard. "
                        + "There is no assumed selector or section-dense seed. The conclusion constructs Y contained in SectionGood(q), of cardinal at most c, "
                        + "with projection injective on Y, Y countably compact and section-dense; its principal extension has CountablyCompactSpace, "
                        + "its fibre adjacency is closed in all X squared, every clique is finite, and for every n there is a finite clique K with K.ncard=n. "
                        + "Hausdorffness is inherited from Ultrafilter A, not an extra conclusion field or a supplied hypothesis in this theorem.")),
                    Paragraph(Text("The proof consumes SectionDenseSelector.exists_countablyCompact_sectionDense_selector q to obtain the actual Y. "
                        + "The preceding principal-extension and closedness theorems then supply the two native topological properties, and the clique theorem "
                        + "supplies finiteness. For exact size n choose a fibre with n <= its ncard, take a subset T of that fibre of exactly n elements, "
                        + "and map T through principalEmbedding. Distinct images are adjacent and injectivity preserves ncard. "
                        + "This includes n=0 with the empty clique, n=1, and every larger prescribed size; there is no uniform finite bound.")),
                    Paragraph(Text("The primary paper's Question 1, printed page 5, asks for a countably compact T1 or Hausdorff space carrying a closed "
                        + "orthogonality relation with finite yet unbounded cliques. Its page 3 requires closure in X squared, including the diagonal. "
                        + "Page 10 partitions a countable discrete set into finite blocks of size n, calls sets meeting each block at most once partial sections, "
                        + "and proposes X=omega union Y for a dense countably compact Y of free ultrafilters containing partial sections. "
                        + "The paper uses the restriction of the ambient closure of the block relation. Here q labels the blocks and its injectivity sets "
                        + "are precisely partial sections; the additional projection-injectivity condition on Y excludes off-principal edges and "
                        + "allows the principal-only fibre relation itself to be closed. For finite fibres, every infinite set has an infinite partial section, "
                        + "so section density meets every nonempty basic clopen in the free remainder. This explains the correspondence of the constructions "
                        + "without treating the paper's conditional existence of Y as an established supplier.")),
                    Paragraph(Text("The exact finite-block parameter map is A = Sigma (fun n : Nat => Fin (n+1)), B=Nat, q=Sigma.fst. "
                        + "The countable sigma of finite types is countable. For each b, q-inverse({b}) equals range(Sigma.mk b): "
                        + "a point in the fibre has first coordinate b, and every Sigma.mk b i lies in it. This range is finite. "
                        + "Injectivity of Sigma.mk b and Set.ncard_range_of_injective identify its ncard with Nat.card(Fin(b+1)); "
                        + "Nat.card_fin gives exactly b+1. For requested n take b=n and use n <= n+1. "
                        + "The endpoint supplies Y and fibreGraph, while T2Space(principalExtension Y) is inherited by the subspace instance. "
                        + "These blocks of sizes 1,2,... merely reindex the nonempty blocks of the paper's size-n partition. "
                        + "For any proposed natural bound N, take the supplied clique K of size N+1. Its finiteness and K.ncard=N+1 contradict K.ncard <= N. "
                        + "Thus this actual X is countably compact, Hausdorff and T1, and its symmetric irreflexive relation is closed in the entire product, "
                        + "has every clique finite and has no uniform finite clique bound. These are exactly the clauses of Question 1. "
                        + "The parameter discharge and the explicit no-bound inference were checked in a transient exact Lean application through the canonical targeted build. "
                        + "This is an application of the existing theorem; it introduces no retained named application theorem or separate Describe.")),
                    Paragraph(Text("The classical method sources have narrower statements: Frolik's Lemma 2.8 requires no accumulation point in the "
                        + "separable metrizable base P, and Lemma 2.9 gives avoidance and omega1 closing-off; Ginsburg-Saks Theorem 2.12 concerns "
                        + "one fixed free-ultrafilter D and completely regular spaces. They are not sources for the exact arbitrary-q selector or this endpoint. "
                        + "The canonical notes distinguish these methods from repository-derived proof composition. "
                        + "The countable finite-block application supplies an affirmative mathematical answer to Question 1; "
                        + "it neither attributes this exact selector construction to the method papers nor addresses Questions 2 and 3. "
                        + "The primary-source status and source-fidelity boundaries are recorded in the Library note and Problems dossier. "
                        + "Open status in the inspected sources does not establish worldwide absence, publication priority or official acceptance."))), DescribeRole.Theorem))));
}
