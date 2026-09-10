using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GraphIrregularity;

internal sealed class RegularLinkIrregularElevenDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/GraphIrregularity/RegularLinkIrregularEleven.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A kernel-checked proof that a known six-regular graph on eleven vertices is link-irregular.",
        H("A Regular Link-Irregular Graph on Eleven Vertices"),
        Blocks(
            Paragraph(Text(
                "Priority. The order-eleven fact is not new here. Jannis Harder reported a "
                    + "six-regular link-irregular graph of order eleven on 14 December 2025, in "
                    + "the discussion thread attached to David Eppstein's post \"Regular "
                    + "link-irregular graphs\", and on 15 December 2025 reported an exhaustive "
                    + "search over all six-regular graphs on eleven vertices yielding four "
                    + "minimal counterexamples, noting that one of them is separated by link "
                    + "degree sequences except for a single pair distinguished by whether its "
                    + "two degree-two vertices are adjacent. The witness used here has that "
                    + "structure and was reported isomorphic to the published one. What this "
                    + "module adds is a kernel-checked proof and a general invariance lemma, "
                    + "not the graph and not the refutation.")),
            Paragraph(Text(
                "Bastien and Khormali, \"On the Regularity, Planarity and Edge Bounds of "
                    + "Link-irregular Graphs\", define: \"A graph G is a link-irregular graph "
                    + "if every two distinct vertices of G have non-isomorphic links. The "
                    + "link of a vertex v in G is the subgraph induced by the neighbors "
                    + "of v in G.\" Thus degrees inside a link are measured within that "
                    + "induced graph, not in the ambient graph.")),
            Paragraph(Text(
                "Section 3 of the arXiv PREPRINT, arXiv:2503.21916v2, prints: "
                    + "\"Conjecture 17. There exists a regular link-irregular graph on n "
                    + "vertices if and only if n >= 12.\" The peer-reviewed version, "
                    + "Discussiones Mathematicae Graph Theory 46(2) (2026) 555-568, "
                    + "DOI 10.7151/dmgt.2619, DOES NOT CONTAIN Conjecture 17; it was "
                    + "removed in revision. The refuted statement is the one printed "
                    + "in the arXiv preprint, not a conjecture published in DMGT.")),
            Paragraph(Text(
                "Only the only-if direction is refuted. The if-direction, asserting "
                    + "existence for every n >= 12, is untouched. Relative to the published "
                    + "results, the contribution is that the smallest known order of a "
                    + "regular link-irregular graph drops from 12 to 11. The paper's "
                    + "Theorem 10 rules out n <= 9; n = 10 remains open. No minimality "
                    + "of 11, classification, or count of such graphs is claimed. The "
                    + "witness graph and invariant are repository constructions; the "
                    + "paper supplies the conjecture, definitions, and n <= 9 exclusion.")),
            Paragraph(Text(
                "For a finite graph, take one round of degree refinement: each vertex "
                    + "contributes its degree paired with the multiset of its neighbors' "
                    + "degrees. Then collect these pairs in an outer multiset. Multiplicities "
                    + "are retained at both levels. The general isomorphism-invariance lemma "
                    + "applies to any finite graphs, independently of this witness.")),
            Paragraph(Text(
                "In the displays, braces and square brackets on binders retain Lean's "
                    + "implicit parameters and typeclass instances. Type* allows an arbitrary "
                    + "universe, independently for each vertex type. SimpleGraph.Iso(H,H') "
                    + "denotes Lean's H ≃g H'; Finset.inter(A,B) denotes A ∩ B. "
                    + "These are notation expansions, with no hypotheses suppressed. "
                    + "Fin(n) has vertices labelled from 0 through n - 1; .val retains "
                    + "the multiset of a finset or projects a subtype to its ambient value.")),
            Definition("wlProfile", "wl-profile", "One round of degree refinement",
                WlProfileFormula(),
                "For H on W, each x contributes its degree and the multiset of degrees "
                    + "of vertices adjacent to x. Mapping the underlying multiset of univ "
                    + "keeps repetitions of equal pairs; the inner map keeps repeated degrees."),
            Describe.Lean(DescribeId.Create("wl-profile-eq-of-iso"),
                DeclarationHandle.Create(Prefix + "wlProfile_eq_of_iso"),
                H("Isomorphisms preserve the refined profile"),
                StatementSource.FromAuthor(IsoInvariantFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The isomorphism f preserves degrees and bijects neighbor sets. "
                        + "Transporting the inner multiset along that neighbor bijection "
                        + "and the outer multiset along f proves equality. W and W' may "
                        + "be different types; all finiteness, equality, and adjacency "
                        + "instances are retained in the statement."))),
                DescribeRole.Theorem),
            Definition("finsetLinkProfile", "finset-link-profile",
                "Compute a link profile in the ambient vertex type",
                FinsetLinkProfileFormula(),
                "For x adjacent to v, its link degree is the cardinality of the intersection "
                    + "of the ambient neighbor finsets of v and x. The inner multiset "
                    + "records the corresponding link degrees of their common neighbors."),
            Describe.Lean(DescribeId.Create("link-degree-eq"),
                DeclarationHandle.Create(Prefix + "link_degree_eq"),
                H("Link degrees from ambient neighbor intersections"),
                StatementSource.FromAuthor(Disp(new Formula.Aligned([
                    GraphParameters("V", "G"),
                    Seq(Typed("v", F.Id("V")), Sp,
                        Typed("x", Call("G.neighborSet", F.Id("v"))), Comma),
                    Seq(Member(Paren(Link("G", "v")), "degree"), Sp, F.Id("x"), Sp, Eq, Sp,
                        Member(Paren(Intersection(F.Id("v"), Member(F.Id("x"), "val"))), "card")),
                ]))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The binder x belongs to G.neighborSet(v), not to an unrestricted "
                        + "ambient vertex type. The induced neighbor finset maps bijectively "
                        + "onto the displayed ambient intersection."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("wl-profile-induce-eq-finset-link-profile"),
                DeclarationHandle.Create(Prefix + "wlProfile_induce_eq_finsetLinkProfile"),
                H("The ambient computation is the induced-link invariant"),
                StatementSource.FromAuthor(Disp(new Formula.Aligned([
                    GraphParameters("V", "G"),
                    Seq(Typed("v", F.Id("V")), Comma),
                    Seq(Call("wlProfile", Link("G", "v")), Sp, Eq, Sp,
                        Call("finsetLinkProfile", F.Id("G"), F.Id("v"))),
                ]))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The equality includes both multiset levels. It transfers the general "
                        + "isomorphism invariant to an ambient computation without erasing "
                        + "multiplicities or changing the induced graph."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "For this witness, the measured plain degree multisets distinguish only "
                    + "10 of the 11 links. The links at vertices 1 and 5 share the degree "
                    + "multiset {2,2,3,3,3,3}. One round of refinement separates all 11 "
                    + "links. This collision is a measured fact about this witness, not "
                    + "a general theorem about regular graphs or graph invariants.")),
            Definition("witnessGraph", "witness-graph", "The explicit eleven-vertex witness",
                Disp(Seq(F.Id("witnessGraph"), Colon, Sp, Call("SimpleGraph", Call("Fin", D(1, 1))),
                    Sp, Eq, Sp, Call("SimpleGraph.fromRel",
                        Seq(F.Id("u"), Sp, F.Id("v"), Sp, Mapsto, Sp,
                            Pair(F.Id("u"), F.Id("v")), Sp, InMacro, Sp, F.Id("witnessEdges"))))),
                "The repository witness has 11 vertices, 33 undirected edges, and degree "
                    + "6 at every vertex. SimpleGraph.fromRel symmetrizes the listed relation "
                    + "and excludes loops. Each edge below is listed once, smaller endpoint first."),
            Paragraph(Text(
                "witnessEdges = [(0,2), (0,4), (0,5), (0,8), (0,9), (0,10), "
                    + "(1,2), (1,3), (1,5), (1,7), (1,8), (1,10), "
                    + "(2,4), (2,5), (2,9), (2,10), "
                    + "(3,6), (3,7), (3,8), (3,9), (3,10), "
                    + "(4,5), (4,6), (4,7), (4,9), (5,6), (5,8), "
                    + "(6,8), (6,9), (6,10), (7,8), (7,9), (7,10)].")),
            Definition("linkProfile", "link-profile", "The witness's link profiles",
                Disp(Seq(Forall, Sp, Typed("v", Call("Fin", D(1, 1))), Comma, Sp,
                    Call("linkProfile", F.Id("v")), Sp, Eq, Sp,
                    Call("finsetLinkProfile", F.Id("witnessGraph"), F.Id("v")))),
                "Each profile is a multiset of pairs of a natural number and a multiset "
                    + "of natural numbers, obtained by specializing finsetLinkProfile."),
            Describe.Lean(DescribeId.Create("witness-regular"),
                DeclarationHandle.Create(Prefix + "witness_regular"),
                H("Every witness vertex has degree six"),
                StatementSource.FromAuthor(Disp(Call("witnessGraph.IsRegularOfDegree", D(6)))),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/ConceptDynamics/harder2025linkirregular")),
                Blocks(Paragraph(Text("Lean proves six-regularity by finite decision."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("witness-profiles-pairwise-ne"),
                DeclarationHandle.Create(Prefix + "witness_profiles_pairwise_ne"),
                H("All eleven refined link profiles are distinct"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), Sp, F.Id("v"), Colon, Sp, Call("Fin", D(1, 1)), Comma, Sp,
                    F.Id("u"), Sp, Neq, Sp, F.Id("v"), Sp, Rightarrow, Sp,
                    Call("linkProfile", F.Id("u")), Sp, Neq, Sp, Call("linkProfile", F.Id("v"))))),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/ConceptDynamics/harder2025linkirregular")),
                Blocks(Paragraph(Text(
                    "The distinctness hypothesis u ≠ v is essential. Lean certifies the "
                        + "universally quantified implication using decide +kernel."))),
                DescribeRole.Theorem),
            Definition("LinkIrregular", "link-irregular", "Pairwise non-isomorphic links",
                Disp(new Formula.Aligned([
                    Seq(GraphParameters("V", "G"), Comma),
                    Seq(Call("LinkIrregular", F.Id("G")), Sp, Iff),
                    Seq(Forall, Sp, F.Id("u"), Sp, F.Id("v"), Colon, Sp, F.Id("V"), Comma, Sp,
                        F.Id("u"), Sp, Neq, Sp, F.Id("v"), Sp, Rightarrow),
                    Call("IsEmpty", Call("SimpleGraph.Iso", Link("G", "u"), Link("G", "v"))),
                ])),
                "IsEmpty asserts that the type of graph isomorphisms between the two "
                    + "induced neighborhoods has no inhabitants. This implements the "
                    + "paper's definition for finite simple graphs."),
            Definition("regularLinkIrregularOnlyFromTwelve", "regular-link-irregular-only-from-twelve",
                "The preprint's only-if direction",
                Disp(new Formula.Aligned([
                    Seq(F.Id("regularLinkIrregularOnlyFromTwelve"), Sp, Iff),
                    Seq(Forall, Sp, Typed("n", F.Id("Nat")), Sp,
                        Typed("G", Call("SimpleGraph", Call("Fin", F.Id("n")))), Sp,
                        Typed("r", F.Id("Nat")), Comma),
                    Seq(D(2), Sp, Leq, Sp, F.Id("n"), Sp, Rightarrow, Sp,
                        Call("G.IsRegularOfDegree", F.Id("r")), Sp, Rightarrow, Sp,
                        Call("LinkIrregular", F.Id("G")), Sp, Rightarrow, Sp,
                        D(1, 2), Sp, Leq, Sp, F.Id("n")),
                ])),
                "The quantifiers cover every order n with at least two vertices, every "
                    + "simple graph on Fin(n), "
                    + "and every natural degree r. Both regularity and link-irregularity "
                    + "are hypotheses. Lean supplies the decidability instances classically "
                    + "inside this closed proposition; the if-direction is not encoded."),
            Describe.Lean(DescribeId.Create("witness-link-irregular"),
                DeclarationHandle.Create(Prefix + "witness_link_irregular"),
                H("The witness has pairwise non-isomorphic links"),
                StatementSource.FromAuthor(Disp(Call("LinkIrregular", F.Id("witnessGraph")))),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/ConceptDynamics/harder2025linkirregular")),
                Blocks(Paragraph(Text(
                    "An isomorphism of two distinct links would equate their wlProfiles. "
                        + "The induced-link equality would then equate their linkProfiles, "
                        + "contradicting witness_profiles_pairwise_ne."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("not-regular-link-irregular-only-from-twelve"),
                DeclarationHandle.Create(Prefix + "not_regularLinkIrregularOnlyFromTwelve"),
                H("The preprint's asserted lower bound is false"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, F.Id("regularLinkIrregularOnlyFromTwelve")))),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/ConceptDynamics/harder2025linkirregular")),
                Blocks(Paragraph(Text(
                    "This closed theorem has no hypotheses. Apply the claimed bound to "
                        + "n = 11, G = witnessGraph, and r = 6. The two witness theorems "
                        + "would imply 12 ≤ 11, a contradiction. This refutes only the "
                        + "only-if direction printed in arXiv:2503.21916v2. It neither "
                        + "establishes nor refutes existence for every n >= 12. Order 10 "
                        + "remains open; 11 is not claimed minimal. No classification or "
                        + "count of regular link-irregular graphs is claimed."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string declaration, string id, string title,
        Formula formula, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Paren(Formula value) => Seq(Open, value, Close);
    private static Formula Member(Formula value, string name) => Seq(value, Dot, F.Id(name));
    private static Formula Pair(Formula left, Formula right) => Seq(Open, left, Comma, Sp, right, Close);
    private static Formula Typed(string name, Formula type) =>
        Paren(Seq(F.Id(name), Colon, Sp, type));
    private static Formula Instance(string name, Formula argument) =>
        Seq(OpenBracket, Call(name, argument), CloseBracket);
    private static Formula TypeStar() => Seq(F.Id("Type"), Star);

    private static Formula GraphParameters(string vertex, string graph) => Seq(
        Forall, Sp, OpenBrace, Sp, F.Id(vertex), Colon, Sp, TypeStar(), Sp, CloseBrace, Sp,
        Instance("Fintype", F.Id(vertex)), Sp, Instance("DecidableEq", F.Id(vertex)), Sp,
        Typed(graph, Call("SimpleGraph", F.Id(vertex))), Sp,
        Instance("DecidableRel", Member(F.Id(graph), "Adj")));

    private static Formula Link(string graph, string vertex) =>
        Call(graph + ".induce", Call(graph + ".neighborSet", F.Id(vertex)));
    private static Formula Intersection(Formula left, Formula right) =>
        Call("Finset.inter", Call("G.neighborFinset", left), Call("G.neighborFinset", right));
    private static Formula LinkDegree(Formula vertex) =>
        Member(Paren(Intersection(F.Id("v"), vertex)), "card");
    private static Formula MapFinset(Formula finset, string variable, Formula value) =>
        Call("Multiset.map", Seq(F.Id(variable), Sp, Mapsto, Sp, value),
            Member(Paren(finset), "val"));

    private static Formula WlProfileFormula() => Disp(new Formula.Aligned([
        Seq(GraphParameters("W", "H"), Comma),
        Seq(Call("wlProfile", F.Id("H")), Sp, Eq),
        MapFinset(Paren(Seq(Member(F.Id("Finset"), "univ"), Colon, Sp,
                Call("Finset", F.Id("W")))), "x",
            Pair(Call("H.degree", F.Id("x")),
                MapFinset(Call("H.neighborFinset", F.Id("x")), "y", Call("H.degree", F.Id("y"))))),
    ]));

    private static Formula FinsetLinkProfileFormula() => Disp(new Formula.Aligned([
        GraphParameters("V", "G"),
        Seq(Typed("v", F.Id("V")), Comma),
        Seq(Call("finsetLinkProfile", F.Id("G"), F.Id("v")), Sp, Eq),
        MapFinset(Call("G.neighborFinset", F.Id("v")), "x",
            Pair(LinkDegree(F.Id("x")),
                MapFinset(Intersection(F.Id("v"), F.Id("x")), "y", LinkDegree(F.Id("y"))))),
    ]));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var parts = name.Split('.');
        var named = new List<Formula> { F.Id(parts[0]) };
        for (var index = 1; index < parts.Length; index++)
            named.AddRange([Dot, F.Id(parts[index])]);
        var items = new List<Formula> { Operatorname, Grp([.. named]), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula IsoInvariantFormula() => Disp(new Formula.Aligned([
        Seq(
            Forall, Sp,
            OpenBrace, Sp,
            F.Id("W"), Sp,
            F.Id("W"), Apos,
            Colon, Sp,
            F.Id("Type"), Star,
            Sp, CloseBrace),
        Seq(
            Grp(), OpenBracket, Call("Fintype", F.Id("W")), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", F.Id("W")), CloseBracket, Sp,
            OpenBracket, Call("Fintype", Seq(F.Id("W"), Apos)), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", Seq(F.Id("W"), Apos)), CloseBracket),
        Seq(
            OpenBrace, Sp,
            F.Id("H"), Colon, Sp,
            Call("SimpleGraph", F.Id("W")),
            Sp, CloseBrace, Sp,
            OpenBrace, Sp,
            F.Id("H"), Apos, Colon, Sp,
            Call("SimpleGraph", Seq(F.Id("W"), Apos)),
            Sp, CloseBrace),
        Seq(
            Grp(), OpenBracket,
            Call("DecidableRel", Member(F.Id("H"), "Adj")),
            CloseBracket, Sp,
            OpenBracket,
            Call("DecidableRel", Member(Seq(F.Id("H"), Apos), "Adj")),
            CloseBracket),
        Seq(
            Open, F.Id("f"), Colon, Sp,
            Call("SimpleGraph.Iso", F.Id("H"), Seq(F.Id("H"), Apos)),
            Close, Comma),
        Seq(
            Call("wlProfile", F.Id("H")),
            Sp, Eq, Sp,
            Call("wlProfile", Seq(F.Id("H"), Apos))),
    ]));
}
