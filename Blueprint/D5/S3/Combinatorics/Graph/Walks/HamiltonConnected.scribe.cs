using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class HamiltonConnectedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict independence and vertex-deletion connectivity give Hamiltonian paths with prescribed distinct endpoints.",
        H("The Chvatal-Erdos Hamilton-connectedness theorem"),
        Blocks(Describe.Lean(DescribeId.Create("hamilton-connectedness"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/HamiltonConnected.exists_isHamiltonian_of_connectivity_independence"),
            H("Every prescribed pair of distinct endpoints"),
            StatementSource.FromAuthor(MainFormula()),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/GraphInvariants/chvatalerdos1972hamiltonian")),
            Blocks(
                Paragraph(Text("For every finite vertex type V in any universe, every simple undirected graph G on V and every natural k, suppose that deleting any set S with S.ncard strictly less than k leaves a connected induced graph. Suppose that every G-independent set S also satisfies S.ncard strictly less than k. For every a and b in V with a distinct from b there exists an actual G.Walk a b visiting each vertex exactly once. Finite enumeration, decidable equality and classical choices are internal proof presentations.")),
                Paragraph(Text("The empty independent set forces k to be positive. Deletion of the empty set supplies an initial path between these same a and b. The finite set of lengths of simple paths with these fixed endpoints has a maximum. No globally longest path with arbitrary endpoints, supplied edge, minimum degree, order lower bound, ambient spanning premise or bound k less than the vertex count is assumed. Empty and singleton orders have no distinct endpoint pair; the construction includes the two-vertex order and every natural k.")),
                Paragraph(Text("Let P be that maximum path and B its actual support. Its vertex count is P.length plus one. If x lies outside B, ConnectivityFan.exists_fan supplies exactly r = min(k, B.card) terminal-clean paths from x to distinct terminals in B, meeting pairwise only at x. The private maximal_path_fan_obstruction assumes neither deletion connectivity nor the independent-set bound. It proves r less than B.card and constructs an independent set containing x with cardinality at least r.")),
                Paragraph(Text("If the fan saturated B, arms ending at P[0] and P[1] would replace the first edge by a detour through x and produce a longer simple path from a to b, including when P has one edge. For the remaining argument exclude the at most one arm ending at b. Each retained terminal has a proved index strictly below P.length and hence a genuine forward successor. Bounded path injectivity makes these successors distinct, and none is x.")),
                Paragraph(Text("An edge from x to a successor replaces its terminal edge by the reversed arm and that edge. An edge between two successors combines the corresponding arms through x and uses OrderedTwoCutSlicing.exists_path_slicing_at_two_ordered_edges. The constructed walk traverses the prefix, the detour, the reversed middle piece, the successor edge and the suffix. Literal slice support disjointness and terminal cleanliness prove simplicity, including adjacent cuts and nil pieces. The resulting path has the same endpoints and length P.length plus detour.length minus one, contradicting maximality.")),
                Paragraph(Text("The independent set is x together with the retained successors. An injection of all arm indices into the optional retained indices proves that adding x compensates for the possible excluded terminal b. Unsaturation forces r = k; the constructed independent set then contradicts the original strict bound. Thus P contains every vertex and is Hamiltonian. This is the original paper's Theorem 3, not an open-problem resolution. Native Menger, fan and slicing results are reused; no complexity bound is asserted."))),
            DescribeRole.Theorem)), []));

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula MainFormula()
    {
        var v = F.Id("V"); var g = F.Id("G"); var k = F.Id("k"); var s = F.Id("S");
        var a = F.Id("a"); var b = F.Id("b"); var p = F.Id("p");
        var connectivity = All("S", Call("Set", v),
            Imp(Lt(Call("ncard", s), k), Call("Connected", Call("induce", g, Call("compl", s)))));
        var independence = All("S", Call("Set", v),
            Imp(Call("IsIndepSet", g, s), Lt(Call("ncard", s), k)));
        var paths = All("a", v, All("b", v,
            Imp(new Formula.Relation(a, FormulaRelationOperator.NotEqual, b),
                Exists("p", Call("Walk", g, a, b), Call("IsHamiltonian", p)))));
        return Disp(All("V", Call("Type"), Imp(Call("Finite", v),
            All("G", Call("SimpleGraph", v), All("k", Call("Nat"),
                Imp(connectivity, Imp(independence, paths)))))));
    }
}
