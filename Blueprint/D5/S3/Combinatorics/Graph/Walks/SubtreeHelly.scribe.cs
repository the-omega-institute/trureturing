using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class SubtreeHellyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pairwise intersecting connected vertex sets in one tree have a common vertex for every nonempty finite family.",
        H("Finite Helly property for subtrees"),
        Blocks(Describe.Lean(DescribeId.Create("finite-subtree-helly"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SubtreeHelly.inter_nonempty_of_pairwise"),
            H("A common vertex for a nonempty finite family"),
            StatementSource.FromAuthor(MainFormula()),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/ConceptDynamics/pr39864subtreehelly")),
            Blocks(
                Paragraph(Text("The universe levels u and v are independent. V is an arbitrary vertex type in Type u, G is a simple undirected graph on V, and I is an arbitrary index type in Type v. The family a maps I to Set(V), and s is a Finset(I). Assume G.IsTree, s.Nonempty, Connected(G.induce(a(i))) for every i in s, and Nonempty(a(i) intersect a(j)) for every i in s and every j in s. Then there exists x in V belonging to a(i) for every i in s, equivalently the intersection indexed by i in s is nonempty. The formula writes this common-intersection conclusion in membership form. The arrow denotes the function type, and inter denotes set intersection.")),
                Paragraph(Text("Only the selected family is finite: neither V nor I is assumed finite. Indices outside s are unrestricted. The pairwise premise includes equal indices. Native Connected includes a nonempty vertex type, and native IsTree includes connectedness and acyclicity. Thus the hypotheses rule out an empty selected fiber and an empty ambient vertex type, rather than adding a finiteness assumption on either carrier.")),
                Paragraph(Text("A connected induced vertex set in a tree contains the unique simple path between any two of its vertices. Indeed, connectedness gives a walk inside the set; erasing repetitions gives a simple path with support contained in that walk. Acyclicity identifies the paths obtained from any two such walks. Consequently the intersection of two preconnected induced vertex sets is preconnected: the common unique path lies in both sets.")),
                Paragraph(Text("For the crossing step, let a and b be connected induced vertex sets with a common pivot m. Join x in a to m inside a and m to y in b inside b. Their appended walk and an arbitrary x-to-y walk have the same reduced simple path. If y lies in a it is already a crossing vertex. Otherwise choose the boundary dart of that simple path leaving a. Its first vertex lies on the arbitrary walk and in a. The dart cannot come from the first walk, whose vertices all lie in a; it therefore comes from the second walk and its first vertex also lies in b. This constructs a vertex of a intersect b on the arbitrary walk.")),
                Paragraph(Text("For three pairwise intersecting connected induced sets a, b and c, choose a point of c intersect a and a point of b intersect c. Connectedness of c gives a walk between them contained in c. Apply the crossing step for a and b to that walk. The crossing vertex belongs to all three sets.")),
                Paragraph(Text("Induct on the positive cardinality of s. A singleton family has a vertex by connectedness. For at least two indices, choose c in s and erase it. Replace each remaining a(i) by a(i) intersect a(c). Each replacement is nonempty by pairwise intersection and preconnected by unique-path convexity, hence connected. Triple Helly supplies pairwise intersections of the replacements. Induction gives a vertex in all replacements; a remaining index also certifies its membership in a(c), giving a vertex in the original entire family.")),
                Paragraph(Text("For a full finite index type I, G.IsTree together with Connected(G.induce(a(i))) for every i and Nonempty(a(i) intersect a(j)) for every i and j implies Nonempty of the intersection over all i. If I is nonempty, apply the finite-family theorem to Finset.univ using a Fintype presentation of Finite(I). If I is empty, that intersection is Set.univ, so its nonemptiness is exactly Nonempty(V), supplied here by G.IsTree.connected.nonempty. Without a nonempty ambient vertex type the empty-family conclusion would fail.")),
                Paragraph(Text("For a common-source feasibility application, take one source space V equipped with one tree G. For each observation i, let a(i) be the subset of source vertices compatible with that observation. For example a(i) can be the fiber over the prescribed value of an observation map on V. For a nonempty finite set s of observations, assume every such feasibility set induces a connected graph in this same G. If every pair admits a common compatible source vertex, the theorem supplies one source vertex compatible with all observations simultaneously. The sets, their memberships and all witnesses refer to this one source; arbitrary pairwise constraint relations on different spaces do not satisfy these hypotheses merely by being pairwise compatible.")),
                Paragraph(Text("The conclusion concerns finite selected families. No infinite-family intersection conclusion or algorithmic resource bound is asserted. The proof source is 8e7's mathlib PR 39864 at immutable revision 12cb0b6433584e454c4d4577472c4792f0dfe5c9, with original file authors Kyle Miller and Rémi Bottinelli. The owning Library note gives the exact declaration correspondence and Apache-2.0 attribution. This is known subtree-Helly mathematics."))),
            DescribeRole.Theorem)), []));

    private static Formula MainFormula()
    {
        var v = F.Id("V"); var g = F.Id("G"); var indices = F.Id("I");
        var a = F.Id("a"); var s = F.Id("s"); var i = F.Id("i"); var j = F.Id("j");
        Formula Fiber(Formula index) => new Formula.Apply(a, [index]);
        var connected = All("i", indices, Imp(Mem(i, s),
            Call("Connected", Call("induce", g, Fiber(i)))));
        var pairwise = All("i", indices, Imp(Mem(i, s), All("j", indices,
            Imp(Mem(j, s), Call("Nonempty", Call("inter", Fiber(i), Fiber(j)))))));
        var common = Ex("x", v, All("i", indices,
            Imp(Mem(i, s), Mem(F.Id("x"), Fiber(i)))));
        return Disp(All("u", Call("Universe"), All("v", Call("Universe"),
            All("V", Call("Type", F.Id("u")), All("G", Call("SimpleGraph", v),
                All("I", Call("Type", F.Id("v")), Imp(Call("IsTree", g),
                    All("a", new Formula.TypeArrow(indices, Call("Set", v)),
                        All("s", Call("Finset", indices), Imp(Call("Nonempty", s),
                            Imp(connected, Imp(pairwise, common))))))))))));
    }

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Mem(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
