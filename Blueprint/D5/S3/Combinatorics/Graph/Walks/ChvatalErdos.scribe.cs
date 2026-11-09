using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class ChvatalErdosDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deletion connectivity at least the independence bound forces a Hamiltonian cycle.",
        H("The Chvatal-Erdos theorem"),
        Blocks(Describe.Lean(DescribeId.Create("hamiltonicity"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/ChvatalErdos.isHamiltonian_of_connectivity_independence"),
            H("Hamiltonicity with vertex-deletion connectivity unfolded"),
            StatementSource.FromAuthor(MainFormula()),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/GraphInvariants/traversogianini2026brooks")),
            Blocks(
                Paragraph(Text("For every finite vertex type V in any universe, every simple undirected graph G on V and every natural number k, assume that V has at least three vertices. Suppose that for every set S with S.ncard less than k the graph induced on the complement of S is connected. Suppose also that every G-independent set has cardinality at most k. Then G is Hamiltonian. A classical finite enumeration and equality decision are presentations of the finite vertex type, not additional mathematical assumptions.")),
                Paragraph(Text("There is no assumption that k be less than the number of vertices. Complete graphs are Hamiltonian under the stated cardinality bound. Otherwise, two nonadjacent vertices give an independent pair and force k to be at least two. This handles k equal to zero or one without inserting a stronger connectivity premise.")),
                Paragraph(Text("Choose a longest ordinary cycle C. If C fails to span V, choose an outside vertex x and a terminal-clean fan of min(k, C.length) paths from x to C. Use the fixed orientation of C to assign each terminal its successor. Native cycle rotations preserve the dart list up to permutation; injectivity of the first and second dart coordinates makes this a single consistent, injective successor assignment.")),
                Paragraph(Text("An edge between two fan successors joins the two corresponding fan paths into a detour and produces a strictly longer actual cycle. An edge from x to a fan successor gives another such detour. Thus no two fan successors are adjacent, no successor is adjacent to x, and no two fan terminals are consecutive. If the fan had fewer than k paths, its minimum-size bound would saturate all vertices of C, contradicting the absence of consecutive terminals. The fan therefore has at least k paths, and x together with its distinct successors is an independent set of more than k vertices, a contradiction.")),
                Paragraph(Text("The detour is spliced on the induced union of its actual support with C and then mapped injectively into G. The maximal cycle is never assumed to be Hamiltonian on the ambient vertex type. The conclusion is existence of a Hamiltonian cycle, with no algorithmic complexity bound or claim about Hamiltonian-connectedness."))),
            DescribeRole.Theorem)), []));

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula MainFormula()
    {
        var v = F.Id("V"); var g = F.Id("G"); var k = F.Id("k"); var s = F.Id("S");
        var connectivity = All("S", Call("Set", v),
            Imp(new Formula.Relation(Call("ncard", s), FormulaRelationOperator.LessThan, k),
                Call("Connected", Call("induce", g, Call("compl", s)))));
        var independence = All("S", Call("Set", v),
            Imp(Call("IsIndepSet", g, s), Le(Call("ncard", s), k)));
        return Disp(All("V", Call("Type"), Imp(Call("Finite", v),
            All("G", Call("SimpleGraph", v), All("k", Call("Nat"),
                Imp(Le(Num(3), Call("card", v)), Imp(connectivity,
                    Imp(independence, Call("IsHamiltonian", g)))))))));
    }
}
