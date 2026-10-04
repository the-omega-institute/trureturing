using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class MorseEnsembleChromaticRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/MorseEnsembleChromaticRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/zheng2026morseensemble");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two graphs on eight vertices have identical independence Morse ensembles and different numbers of proper four-colourings. Thus the chromatic polynomial is not a function of the independence Morse ensemble.",
        H("The independence Morse ensemble does not determine the chromatic polynomial"),
        Blocks(
            Node("independenceComplex", "The nonempty independence complex", IndependenceFormula(),
                "Definition 6.1 (p. 24): \"For a graph G = (V, E), the independence complex Ind(G) = {I ⊆ V | I independent in G} is a simplicial complex of dimension α(G)−1, where α(G) is the independence number, the size of the largest independent set.\" The vertices are Fin n. Only nonempty independent sets are faces; the empty set is excluded from the face poset, as in the dimension-indexed Morse vector. IsIndepSet is Mathlib's predicate, and the coercion in the formula is from a finite set to a set of vertices."),
            Node("coveringPairs", "Covering pairs", CoversFormula(),
                "Section 2 (pp. 3–4): \"The face poset P(K) of a finite simplicial complex K is the partially ordered set of all simplices of K, ordered by inclusion. Its covering relations are precisely the pairs σ ≺ τ with σ ⊂ τ and dim τ = dim σ + 1.\" Face cardinality is dimension plus one. The product is the Cartesian product of finite sets."),
            Node("Compatible", "Disjoint endpoint faces", CompatibleFormula(),
                "Two distinct covering pairs can belong to the same matching exactly when their endpoint faces are all different. The four inequalities compare the first and second coordinates of the two pairs."),
            Node("Acyclic", "A finite topological ranking", AcyclicFormula(),
                "A natural-valued rank strictly increases along every arrow whose endpoints lie in S. On a finite set this is equivalent to absence of a nonempty directed cycle. The rank is a certificate, and different ranks for the same matching are not counted as different matchings."),
            Node("acyclicMatchings", "All acyclic matchings, each once", MatchingsFormula(),
                "Section 2 (p. 4): \"An acyclic matching on P(K) is a collection M of covering pairs (σ, τ) such that each simplex of K appears in at most one pair and such that the Hasse diagram, after reversing the matched edges, contains no directed cycle [12].\" The powerset lists subsets of C exactly once. The filter imposes the four endpoint inequalities and the strictly increasing ranking condition. In the independence complex, C is coveringPairs F. The displayed arrow relation points upward on matched pairs and downward on the remaining pairs. Certificates distinguish acyclic and cyclic candidates, but the coefficients count matchings, not certificates."),
            Node("Critical", "Critical faces", CriticalFormula(),
                "Section 2 (p. 4): \"The simplices not appearing in any pair of M are called critical. We write c_i(M) for the number of critical i-simplices.\" A face is critical if it is unequal to either coordinate of every matching pair."),
            Node("alpha", "Largest face cardinality", AlphaFormula(),
                "The maximum face cardinality is the supremum of card over the finite set F, with value zero for the empty complex. For the independence complex this is α(G), the independence number."),
            Node("criticalCount", "Critical simplices in each dimension", CountFormula(),
                "Critical i-simplices have cardinality i+1. Each face is counted once, without quotienting by graph automorphisms."),
            Node("morseVector", "The whole Morse vector", VectorFormula(),
                "The list contains the critical counts in dimensions 0 through alpha F minus one, in this order. Its length is alpha F, and an empty complex has the empty vector. Lists provide a common carrier for graphs with different numbers of vertices."),
            Node("ensemble", "Morse-vector multiplicities", EnsembleFormula(),
                "Definition 1.1 (p. 2): \"The Morse ensemble polynomial of K is\" ME_K(z_0, …, z_d) = Σ_{M ∈ A(K)} Π_{i=0}^{d} z_i^{c_i(M)}, \"where A(K) denotes the set of all acyclic matchings on P(K).\" The finitely supported natural-valued function ensemble records precisely each entire exponent vector's coefficient: single(v,1) contributes one at v and zero elsewhere. The formula displays its defining sum, not an evaluation at particular values of the polynomial variables."),
            Node("Phi", "The independence Morse ensemble", PhiFormula(),
                "Definition 6.1 (p. 24): \"We define the independence ME polynomial\" Φ(G) := ME_{Ind(G)}(z_0, z_1, …, z_{α(G)−1}), \"the Morse ensemble polynomial of the independence complex of G.\" Phi is its complete Morse-vector coefficient data. The nonempty independence complex supplies the faces and covering pairs."),
            Node("chromaticCount", "Proper colourings with labelled colours", ChromaticFormula(),
                "chromaticCount G k is χ(G; k), the number of functions Fin n → Fin k assigning unequal colours to adjacent vertices. Colours are labelled, and colour permutations are not quotiented out. The edge condition is Mathlib's Coloring condition; positivity is equivalent to G.Colorable k."),
            Node("claim", "Zheng's recovery question", ClaimFormula(),
                "Open problem (4), p. 29: \"Recovery from Φ(G). Theorem 6.4 shows that Φ(G) determines ME_G, and hence the Laplacian spectrum of G. Which further graph parameters are functions of Φ(G)? For instance, is the chromatic polynomial χ(G; t) always recoverable from Φ(G)?\" The quantified assertion says that any two finite simple graphs with equal entire Phi data have equal proper-colouring counts at every natural k. Equality of chromatic polynomials implies these equalities, so a counterexample at k=4 answers the printed question negatively. The quantification includes arbitrary n and m, including the empty graph."),
            Describe.Lean(DescribeId.Create("morse-result"), DeclarationHandle.Create(Prefix + "result"),
                H("A negative answer"), StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Let Hone have edges 01, 07, 12, 23, 27, 34, 47, 56, and Htwo have edges 03, 04, 12, 17, 25, 26, 57, 67, on vertices 0 through 7. Take their complements Gone and Gtwo. Their nonempty independence complexes consist of the eight vertices and eight edges of Hone and Htwo. Each has acyclic-matching size counts [1,16,102,332,581,516,180,0,0]; a matching of size r has Morse vector [8−r,8−r], so Phi Gone = Phi Gtwo. The colouring [0,0,1,1,2,3,3,2] proves Gone is four-colourable. The vertices {1,3,4,5,6} form a five-clique in Gtwo, so chromaticCount Gtwo 4 = 0. Thus the common Phi does not determine the chromatic polynomial. Private certificate lists assign a natural-valued rank or directed cycle to each candidate; every code is checked against its matching, and exhaustive enumeration and uniqueness are proved. The count 72 and the full chromatic polynomials are not asserted by this theorem."))),
                DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("morse-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Eqn(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => Rel(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iffn(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula All(string v, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(v), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Ex(string v, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(F.Id(v), Colon, Sp, type)), Comma, Sp, body);
    private static Formula AllIn(string v, Formula set, Formula body) =>
        Seq(Forall, Sp, F.Id(v), Sp, InMacro, Sp, set, Comma, Sp, body);
    private static Formula Lam(string v, Formula type, Formula body) =>
        Seq(Parenthesized(Seq(F.Id(v), Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula Instance(string name, Formula arg, Formula body) =>
        Seq(OpenBracket, Call(name, arg), CloseBracket, Comma, Sp, body);
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Prop => Named("Prop");
    private static Formula Type => Named("Type");
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Set(Formula t) => Call("Set", t);
    private static Formula Fs(Formula t) => Call("Finset", t);
    private static Formula Face => Fs(Fin(F.Id("n")));
    private static Formula Faces => Fs(Face);
    private static Formula PairType(Formula t) => Seq(t, Sp, Times, Sp, t);
    private static Formula Pairs => Fs(Parenthesized(PairType(Face)));
    private static Formula Graph(Formula n) => Call("SimpleGraph", Fin(n));
    private static Formula Fn(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Tuple(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Coord(Formula p, byte i) => new Formula.Subscript(p, D(i));
    private static Formula Card(Formula s) => Call("card", s);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mem(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Negn(Formula a) => new Formula.Not(Parenthesized(a));
    private static Formula Filter(Formula s, string v, Formula type, Formula p) => Call("filter", s, Lam(v, type, p));
    private static Formula Pairwise(Formula m) => AllIn("p", m, AllIn("q", m,
        Imp(Ne(F.Id("p"), F.Id("q")), Call("Compatible", F.Id("p"), F.Id("q")))));
    private static Formula Reversed(Formula c, Formula m) => Lam("a", F.Id("A"), Lam("b", F.Id("A"),
        Or(Mem(Tuple(F.Id("a"), F.Id("b")), m),
            And(Mem(Tuple(F.Id("b"), F.Id("a")), c), Negn(Mem(Tuple(F.Id("b"), F.Id("a")), m))))));
    private static Formula WithGraph(Formula body) => All("n", N, All("G", Graph(F.Id("n")),
        Instance("DecidableRel", Call("Adj", F.Id("G")), body)));
    private static Formula WithFaces(Formula body) => All("n", N, All("F", Faces, body));
    private static Formula WithMatching(Formula body) => WithFaces(All("M", Pairs, body));

    private static Formula IndependenceFormula() => WithGraph(Eqn(Call("independenceComplex", F.Id("G")),
        Filter(Named("univ"), "s", Face, And(Call("Nonempty", F.Id("s")),
            Call("IsIndepSet", F.Id("G"), Seq(Parenthesized(Seq(Call("coe", F.Id("s")), Colon, Sp, Set(Fin(F.Id("n")))))))))));

    private static Formula CoversFormula() => WithFaces(Eqn(Call("coveringPairs", F.Id("F")),
        Filter(Call("product", F.Id("F"), F.Id("F")), "p", Parenthesized(PairType(Face)),
            And(Seq(Coord(F.Id("p"), 1), Sp, Subset, Sp, Coord(F.Id("p"), 2)),
                Eqn(Card(Coord(F.Id("p"), 2)), Add(Card(Coord(F.Id("p"), 1)), D(1)))))));

    private static Formula CompatibleFormula() => All("A", Type,
        Instance("DecidableEq", F.Id("A"), All("p", PairType(F.Id("A")), All("q", PairType(F.Id("A")),
            Iffn(Call("Compatible", F.Id("p"), F.Id("q")),
                And(Ne(Coord(F.Id("p"), 1), Coord(F.Id("q"), 1)),
                    And(Ne(Coord(F.Id("p"), 1), Coord(F.Id("q"), 2)),
                        And(Ne(Coord(F.Id("p"), 2), Coord(F.Id("q"), 1)), Ne(Coord(F.Id("p"), 2), Coord(F.Id("q"), 2))))))))));

    private static Formula AcyclicFormula() => All("A", Type, All("S", Fs(F.Id("A")),
        All("R", Fn(F.Id("A"), Fn(F.Id("A"), Prop)), Iffn(Call("Acyclic", F.Id("S"), F.Id("R")),
            Ex("rank", Fn(F.Id("A"), N), AllIn("a", F.Id("S"), AllIn("b", F.Id("S"),
                Imp(new Formula.Apply(F.Id("R"), [F.Id("a"), F.Id("b")]),
                    Rel(new Formula.Apply(F.Id("rank"), [F.Id("a")]), FormulaRelationOperator.LessThan,
                        new Formula.Apply(F.Id("rank"), [F.Id("b")]))))))))));

    private static Formula MatchingsFormula() => All("A", Type, Instance("DecidableEq", F.Id("A"),
        All("F", Fs(F.Id("A")), All("C", Fs(Parenthesized(PairType(F.Id("A")))),
            Eqn(Call("acyclicMatchings", F.Id("F"), F.Id("C")),
                Filter(Call("powerset", F.Id("C")), "M", Fs(Parenthesized(PairType(F.Id("A")))),
                    And(Pairwise(F.Id("M")), Call("Acyclic", F.Id("F"), Reversed(F.Id("C"), F.Id("M"))))))))));

    private static Formula CriticalFormula() => All("n", N, All("M", Pairs, All("s", Face,
        Iffn(Call("Critical", F.Id("M"), F.Id("s")), AllIn("p", F.Id("M"),
            And(Ne(F.Id("s"), Coord(F.Id("p"), 1)), Ne(F.Id("s"), Coord(F.Id("p"), 2))))))));

    private static Formula AlphaFormula() => WithFaces(Eqn(Call("alpha", F.Id("F")), Call("sup", F.Id("F"), Named("card"))));
    private static Formula CountFormula() => WithMatching(All("i", N, Eqn(Call("criticalCount", F.Id("F"), F.Id("M"), F.Id("i")),
        Card(Filter(F.Id("F"), "s", Face, And(Eqn(Card(F.Id("s")), Add(F.Id("i"), D(1))), Call("Critical", F.Id("M"), F.Id("s"))))))));
    private static Formula VectorFormula() => WithMatching(Eqn(Call("morseVector", F.Id("F"), F.Id("M")),
        Call("map", Call("criticalCount", F.Id("F"), F.Id("M")), Call("range", Call("alpha", F.Id("F"))))));
    private static Formula EnsembleFormula() => WithFaces(All("C", Pairs,
        Eqn(Call("ensemble", F.Id("F"), F.Id("C")), Seq(F.Sum, Underscore,
            Grp(Mem(F.Id("M"), Call("acyclicMatchings", F.Id("F"), F.Id("C")))), Sp,
            Call("single", Call("morseVector", F.Id("F"), F.Id("M")), D(1))))));
    private static Formula PhiFormula() => WithGraph(Eqn(Call("Phi", F.Id("G")),
        Call("ensemble", Call("independenceComplex", F.Id("G")), Call("coveringPairs", Call("independenceComplex", F.Id("G"))))));
    private static Formula ChromaticFormula() => WithGraph(All("k", N, Eqn(Call("chromaticCount", F.Id("G"), F.Id("k")),
        Card(Filter(Named("univ"), "c", Fn(Fin(F.Id("n")), Fin(F.Id("k"))),
            All("a", Fin(F.Id("n")), All("b", Fin(F.Id("n")),
                Imp(Call("Adj", F.Id("G"), F.Id("a"), F.Id("b")),
                    Ne(new Formula.Apply(F.Id("c"), [F.Id("a")]), new Formula.Apply(F.Id("c"), [F.Id("b")]))))))))));
    private static Formula ClaimFormula() => Iffn(F.Id("claim"), All("n", N, All("m", N,
        All("G", Graph(F.Id("n")), All("H", Graph(F.Id("m")),
            Imp(Eqn(Call("Phi", F.Id("G")), Call("Phi", F.Id("H"))),
                All("k", N, Eqn(Call("chromaticCount", F.Id("G"), F.Id("k")), Call("chromaticCount", F.Id("H"), F.Id("k"))))))))));
}
