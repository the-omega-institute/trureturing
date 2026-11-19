using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Chordal;

internal sealed class GainPotentialDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Triangle-compatible group labels on a finite chordal graph admit a global vertex potential.",
        H("Group potentials from triangle consistency"),
        Blocks(
            Paragraph(Text("Let G be a finite simple graph and H an arbitrary group. The label g(i,j) is attached to the oriented edge from i to j. Reversal inverts the label. On each triangle, the ordered product g(i,j)g(j,k) equals g(i,k). A potential assigns a group element to each vertex so that every edge label is the inverse source potential multiplied by the target potential.")),
            Describe.Lean(
                DescribeId.Create("chordal-gain-potential"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Chordal/GainPotential.exists_gain_potential"),
                H("A global potential on every finite chordal graph"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Chordality means that every cycle of length at least four has a chord. The group may be noncommutative, and the vertex type may lie in any universe. The theorem includes the empty graph and graphs with several connected components. The gain function is total, but its values on nonedges and on the diagonal are unrestricted.")),
                    Paragraph(Text("Induct on a finite set of vertices. A simplicial vertex x has pairwise adjacent neighbors in the induced graph. Remove x and obtain a potential psi on the remaining vertices. If x has no remaining neighbor, its potential can be assigned freely. Otherwise choose a neighbor w and set the potential at x to psi(w) times the inverse of g(x,w). For each other neighbor j, simpliciality supplies the edge from w to j, and the triangle relation shows that this same assignment satisfies the edge from x to j. Reversal supplies the opposite orientation. Reinsert x without changing any of the other potential values.")),
                    Paragraph(Text("The argument uses associativity and inverses without commuting factors. It applies to phase synchronization by taking a phase group, and to permutation synchronization by taking a permutation group. These interpretations require the stated exact triangle relations. They supply no estimate for inconsistent or noisy labels, no uniqueness across components, and no algorithmic running-time bound.")),
                    Paragraph(Text("Group gains, balance and switching are classical gain-graph notions. Zaslavsky's Lectures on Gain Graphs and Hyperplane Arrangements, Definitions 1, 3, 4 and 10 and Propositions 7, 11, 12 and 13, describe their background: https://people.math.binghamton.edu/zaslav/Tpapers/gaingraphs-lecture-notes.pdf . Here the sufficient local condition is triangle consistency on a chordal graph."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula P(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(P(a), FormulaLogicOperator.Implies, P(b));
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mul(Formula a, Formula b) => Seq(a, Sp, Star, Sp, b);

    private static Formula Statement()
    {
        var v = F.Id("V");
        var h = F.Id("H");
        var graph = F.Id("G");
        var i = F.Id("i");
        var j = F.Id("j");
        var k = F.Id("k");
        Formula adj(Formula a, Formula b) => Call("Adj", graph, a, b);
        Formula gain(Formula a, Formula b) => Call("g", a, b);
        Formula pot(Formula a) => Call("phi", a);
        var reversal = All("i", v, All("j", v,
            Imp(adj(i, j), Eqn(gain(j, i), Call("inv", gain(i, j))))));
        var triangle = All("i", v, All("j", v, All("k", v,
            Imp(adj(i, j), Imp(adj(j, k), Imp(adj(i, k),
                Eqn(Mul(gain(i, j), gain(j, k)), gain(i, k))))))));
        var conclusion = Some("phi", new Formula.TypeArrow(v, h),
            All("i", v, All("j", v, Imp(adj(i, j),
                Eqn(gain(i, j), Mul(Call("inv", pot(i)), pot(j)))))));
        return All("V", Call("Type", F.Id("u")),
            All("H", Call("Type", F.Id("v")),
                Seq(OpenBracket, Call("Finite", v), CloseBracket, Sp,
                    OpenBracket, Call("Group", h), CloseBracket, Comma, Sp,
                    All("G", Call("SimpleGraph", v),
                        All("g", new Formula.TypeArrow(v, new Formula.TypeArrow(v, h)),
                            Imp(Call("IsChordal", graph),
                                Imp(reversal, Imp(triangle, conclusion))))))));
    }
}
