using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class MandalMannaDQDilworthRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Eigenstructure/mandalmanna2026distance");

    public DocumentDefinition Create()
    {
        Formula a = V("a"), rest = V("rest"), v = V("V"), g = V("G"), u = V("u"), w = V("v");
        Formula alpha = V("alpha"), i = V("i"), k = V("k"), n = V("n");
        Formula listNat = Call("List", C("Nat")), nil = Qualified("List", "nil");
        Formula cons = App(Qualified("List", "cons"), a, rest);
        Formula vertices = new Formula.Aligned([
            Eqn(Call("Vertices", nil), C("PEmpty")),
            All("a", C("Nat"), All("rest", listNat,
                Eqn(Call("Vertices", cons), Call("Sum", Call("Vertices", rest), Call("Fin", a)))))
        ]);
        Formula reverseGraph = new Formula.Aligned([
            Eqn(Call("reverseCGraph", nil), Cast(Qualified("Bot", "bot"), Call("SimpleGraph", C("PEmpty")))),
            All("a", C("Nat"), All("rest", listNat,
                Eqn(Call("reverseCGraph", cons), App(Qualified("Compl", "compl"),
                    App(Qualified("SimpleGraph", "sum"), Call("reverseCGraph", rest),
                        Cast(Qualified("Top", "top"), Call("SimpleGraph", Call("Fin", a))))))))
        ]);
        Formula blockIndex = new Formula.Aligned([
            All("v", C("PEmpty"), Eqn(Call("blockIndex", nil, w), Call("nomatch", w))),
            All("a", C("Nat"), All("rest", listNat, All("v", Call("Vertices", rest),
                Eqn(Call("blockIndex", cons, App(Qualified("Sum", "inl"), w)),
                    Call("blockIndex", rest, w))))),
            All("a", C("Nat"), All("rest", listNat, All("i", Call("Fin", a),
                Eqn(Call("blockIndex", cons, App(Qualified("Sum", "inr"), i)),
                    Add(App(Qualified("List", "length"), rest), D(1))))))
        ]);
        Formula transmission = Carrier(true, false, All("G", Call("SimpleGraph", v), All("u", v,
            Eqn(Call("transmission", g, u), Seq(
                new Formula.Subscript(Sum, Seq(w, Colon, Sp, v)), Sp,
                Cast(App(Qualified("SimpleGraph", "dist"), g, u, w), C("Real")))))));
        Formula distanceSignless = Carrier(true, true, All("G", Call("SimpleGraph", v),
            Eqn(Call("distanceSignless", g), Add(
                App(Qualified("Matrix", "diagonal"), Call("transmission", g)),
                App(Qualified("Matrix", "of"), Lam("u", v, Lam("v", v,
                    Cast(App(Qualified("SimpleGraph", "dist"), g, u, w), C("Real")))))))));
        Formula vicinal = Carrier(false, false, All("G", Call("SimpleGraph", v), All("u", v, All("v", v,
            Eqn(Call("vicinal", g, u, w), new Formula.Relation(
                App(Qualified("SimpleGraph", "neighborSet"), g, u), FormulaRelationOperator.SubsetOf,
                Call("insert", w, App(Qualified("SimpleGraph", "neighborSet"), g, w))))))));
        Formula c = V("c");
        Formula cover = Carrier(false, false, All("G", Call("SimpleGraph", v), All("k", C("Nat"),
            Eqn(Call("HasChainCover", g, k), Some("c", Fn(v, Call("Fin", k)), All("u", v, All("v", v,
                Imp(Eqn(App(c, u), App(c, w)),
                    Or(Call("vicinal", g, u, w), Call("vicinal", g, w, u))))))))));
        Formula dilworth = Carrier(false, false, All("G", Call("SimpleGraph", v),
            Eqn(Call("dilworthNumber", g), Call("sInf", SetOf("k", C("ENat"),
                Some("n", C("Nat"), And(Eqn(k, Cast(n, C("ENat"))), Call("HasChainCover", g, n))))))));
        Formula multiplicity = Carrier(true, true, All("G", Call("SimpleGraph", v), All("theta", C("Real"),
            Eqn(Call("multiplicity", g, V("theta")),
                App(Qualified("Polynomial", "rootMultiplicity"), V("theta"),
                    App(Qualified("Matrix", "charpoly"), Call("distanceSignless", g)))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Eight vertices give nonlocal distance-signless multiplicity above vicinal width.",
            H("A repeated distance-signless eigenvalue in a single vicinal chain"), Blocks(
                Node("Vertices", "Recursive vertex carrier", vertices,
                    "Section 1, page 2: “where ∪ denotes disjoint union and the overline denotes graph complementation. They call G = C(α₁,…,αₘ) a 𝒞-graph, and (α₁,…,αₘ) its creation sequence.” The empty carrier is PEmpty. Each new block contributes Fin a on the right of a disjoint sum; the newest block is stored first in the recursive list.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("reverseCGraph", "Complement and disjoint-union recurrence", reverseGraph,
                    "Section 1, page 2: “where ∪ denotes disjoint union and the overline denotes graph complementation. They call G = C(α₁,…,αₘ) a 𝒞-graph, and (α₁,…,αₘ) its creation sequence.” The empty graph is auxiliary. SimpleGraph.sum is disjoint union; Top.top is the complete graph and Compl.compl complements the entire sum. Thus the first nonempty stage is the complement of the complete first block.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("cGraph", "Chronological creation sequence",
                    All("alpha", listNat, Eqn(Call("cGraph", alpha),
                        Call("reverseCGraph", App(Qualified("List", "reverse"), alpha)))),
                    "Section 1, page 2: “where ∪ denotes disjoint union and the overline denotes graph complementation. They call G = C(α₁,…,αₘ) a 𝒞-graph, and (α₁,…,αₘ) its creation sequence.” Reversing the input once makes alpha chronological while retaining structural recursion on its reverse.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("blockIndex", "One-based chronological block index", blockIndex,
                    "The creation sequence (α₁,…,αₘ) in Section 1, page 2 indexes blocks from one. An old vertex retains its index; a vertex in the new block has index length rest + 1. The empty case eliminates its impossible vertex.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("transmission", "Transmission from native distances", transmission,
                    "Section 1, page 1: “The sum of the distances between a vertex v and every other vertex in G is known as the transmission of v and denoted by Tr(v), that is,” followed by the row-sum display. Here the fixed vertex is u and the summation vertex is v, correcting the display's inconsistent dummy names using the preceding sentence. Each natural distance is coerced to Real before summation.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("distanceSignless", "Distance signless Laplacian", distanceSignless,
                    "Section 1, page 1: “D^Q(G) = Tr(G) + D(G)”. The diagonal contains the transmission, and the distance matrix has the native SimpleGraph.dist entries coerced to Real. Fintype and DecidableEq are implicit typeclass parameters.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("vicinal", "Vicinal comparison", vicinal,
                    "Definition 5.1, page 10: “For a graph G, define u ≼ v if N(u) ⊆ N[v] (equivalently, N[u] ⊆ N[v] when u ∼ v, and N(u) ⊆ N(v) when u ≁ v).” The closed neighborhood is insert v (G.neighborSet v).",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("HasChainCover", "Finite cover by vicinal chains", cover,
                    "Definition 5.1, page 10: “A set of vertices pairwise related by ≼ is a chain; a set of pairwise unrelated is an antichain.” A function c assigns each vertex a label in Fin k. Its fibers cover every vertex, and each fiber consists of pairwise comparable vertices. Unused labels are permitted.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("dilworthNumber", "Minimum number of vicinal chains", dilworth,
                    "Definition 5.1, page 10: “The Dilworth number ∇(G) is the minimum number of chains needed to cover V(G), equivalently (by Dilworth’s theorem) the maximum size of an antichain.” The infimum is in ENat; an empty feasible set has value infinity. On the finite source graphs singleton chains give a finite cover, so this infimum is the ordinary minimum.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("localExceptions", "Block-local exceptional eigenvalues", LocalExceptions(),
                    "Section 5, page 11: “𝒯^Q(G) = {Trᵢ−1 : i odd, αᵢ≥2} ∪ {Trᵢ−2 : i even, αᵢ≥2}.” A Fin alpha.length index i denotes source block i.val + 1; the block size must be at least two. A representative vertex of that block supplies its transmission. The shifts are subtraction in Real.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("multiplicity", "Algebraic eigenvalue multiplicity", multiplicity,
                    "Conjecture 5.5, page 11 uses mult_{D^Q(G)}(θ). This is Polynomial.rootMultiplicity of theta in the native characteristic polynomial of distanceSignless G. A characteristic polynomial is monic, so its zero-polynomial totalization never enters. Algebraic multiplicity is at least eigenspace dimension, which suffices for the refutation.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("claim", "Conjecture 5.5", Eqn(Call("claim"), Parenthesized(ClaimBody())),
                    "Conjecture 5.5, page 11: “For every connected 𝒞-graph G, every eigenvalue of D^Q(G) not in 𝒯^Q(G) satisfies mult_{D^Q(G)}(θ) ≤ ∇(G).” Section 2, page 3: “Throughout, G is a connected 𝒞-graph on n vertices with creation sequence (α₁,…,αₘ), nᵢ = α₁+⋯+αᵢ, and αₘᵢₙ = min₁≤ᵢ≤ₘ αᵢ and m is even.” Here alpha ranges over positive lists of even length at least two, G is cGraph alpha, theta is real, and the eigenvalue is for Matrix.toLin' of its distance signless matrix. The natural algebraic multiplicity is coerced to ENat for comparison with dilworthNumber.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("result", "Refutation with eight singleton blocks", Seq(Neg, Sp, Parenthesized(ClaimBody())),
                    "The source recurrence with eight singleton blocks gives a connected graph with a universal vertex. Its vertices fit in one vicinal chain, and no zero-chain cover exists. Two independent global modes of its distance signless matrix have eigenvalue 8, so its algebraic multiplicity is at least two. All creation blocks have size one, making the local-exception set empty. Consequently this eigenvalue violates the proposed upper bound of one. The proof obtains the two modes from parameterized shifted matrices: their kernel identities hold for every natural R, and independence holds for R ≥ 1. Identification with native recurrence graphs is proved at R = 2 only; the uniform native-graph extension and exact multiplicity two uniformly remain open. The D^L results, local-mode and quotient formulas, and Example 5.4 are not refuted by this witness.",
                    DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));
    }

    private static Formula LocalExceptions()
    {
        Formula alpha = V("alpha"), i = V("i"), v = V("v"), theta = V("theta");
        Formula j = Add(Call("val", i), D(1));
        Formula graph = Call("cGraph", alpha);
        return All("alpha", Call("List", C("Nat")), Eqn(Call("localExceptions", alpha),
            SetOf("theta", C("Real"), Some("i", Call("Fin", App(Qualified("List", "length"), alpha)),
                And(Leq(D(2), Seq(alpha, OpenBracket, i, CloseBracket)),
                    Some("v", Call("Vertices", App(Qualified("List", "reverse"), alpha)),
                        And(Eqn(Call("blockIndex", App(Qualified("List", "reverse"), alpha), v), j),
                            Or(And(Call("Odd", j), Eqn(theta, Sub(Call("transmission", graph, v), D(1)))),
                                And(Call("Even", j), Eqn(theta, Sub(Call("transmission", graph, v), D(2))))))))))));
    }

    private static Formula ClaimBody()
    {
        Formula alpha = V("alpha"), theta = V("theta"), i = V("i");
        Formula length = App(Qualified("List", "length"), alpha), graph = Call("cGraph", alpha);
        return All("alpha", Call("List", C("Nat")), Imp(Leq(D(2), length),
            Imp(Call("Even", length), Imp(
                All("i", Call("Fin", length), Lt(D(0), Seq(alpha, OpenBracket, i, CloseBracket))),
                Imp(App(Qualified("SimpleGraph", "Connected"), graph), All("theta", C("Real"),
                    Imp(App(Qualified("Module", "End", "HasEigenvalue"),
                            App(Seq(Qualified("Matrix", "toLin"), Apos), Call("distanceSignless", graph)), theta),
                        Imp(new Formula.Not(new Formula.Relation(theta, FormulaRelationOperator.MemberOf, Call("localExceptions", alpha))),
                            Leq(Cast(Call("multiplicity", graph, theta), C("ENat")),
                                Call("dilworthNumber", graph))))))))));
    }

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("mandal-manna-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role);
    private static Formula Carrier(bool finite, bool decidable, Formula body)
    {
        Formula tail = decidable ? Seq(OpenBracket, Call("DecidableEq", V("V")), CloseBracket, Sp, body) : body;
        return All("V", C("Type"), finite ? Seq(OpenBracket, Call("Fintype", V("V")), CloseBracket, Sp, tail) : tail);
    }
    private static Formula SetOf(string name, Formula type, Formula body) =>
        Seq(OpenBrace, V(name), Colon, Sp, type, Sp, Mid, Sp, body, CloseBrace);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Seq(C("fun"), Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula V(string name) => F.Id(name);
    private static Formula C(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Qualified(params string[] names) => Seq(names.Select(C)
        .SelectMany((name, index) => index == 0 ? new[] { name } : new[] { Dot, name }).ToArray());
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? C(name) : App(C(name), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Fn(Formula from, Formula to) => new Formula.TypeArrow(from, to);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Eqn(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Leq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Or(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Or, right);
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
