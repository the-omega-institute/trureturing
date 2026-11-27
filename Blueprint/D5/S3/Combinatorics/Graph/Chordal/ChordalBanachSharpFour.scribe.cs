using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Chordal;

internal sealed class ChordalBanachSharpFourDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite connected chordal graphs force real Banach reconstruction errors arbitrarily close to four.",
        H("Sharpness of the chordal Banach reconstruction constant"),
        Blocks(
            Paragraph(Text("Write Skew(V,g) for skew symmetry on every ordered pair of vertices, and Flat(G,g) for the condition that the norm of the sum of the first two oriented gains minus the third gain is at most one on every ordered triangle of G. Write Error(g,p,u,v) for the norm of the gain on the oriented edge from u to v minus the potential difference p(v) minus p(u).")),
            Describe.Lean(DescribeId.Create("sharp-chordal-banach-lower-bound"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Chordal/ChordalBanachSharpFour.exists_chordal_banach_gain_lower_four"),
                H("Errors approach four"), StatementSource.FromAuthor(Disp(LowerBound())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Build a finite graph by attaching complete blocks along the union of nested surviving subsets of the last several blocks. The surviving subsets form a clique. A deepest vertex on any cycle of length at least four therefore has adjacent cycle neighbours. The construction includes every permitted retention choice and multiple copies of each descendant history.")),
                    Paragraph(Text("On oriented chains use the supremum of absolute evaluations by cochains bounded by three on edges and by one on triangles. Signed coordinate evaluations bound the chain mass by three times this norm. The supported chains of boundary zero form a finite-dimensional real Banach space. Rooted paths correct the edge generators into cycles, and changing a potential adds a cycle to each rooted path chain.")),
                    Paragraph(Text("Translate the chain potentials by their mean over the root block and average over graph symmetries. Project to ancestral spines. The norm error of changing the projection is controlled by the mass in a single descendant copy, which tends to zero as the number of copies grows. The remaining changes in retention ages and the effect of distinguishing a parent vertex are controlled by the ratio of the retained sizes.")),
                    Paragraph(Text("On the band of ages, centered residue indicators give a skew triangle-flat cochain for each residue. An edge of the full width in its residue path contributes two minus two over the width. Two distinguished vertices add two to the ideal band expression. The refinement estimates bound the difference between that expression and the evaluation of the actual residual. The potential terms telescope on each residue path and cancel between residues. Increasing the width, the number of full-width steps, and the retention and copy parameters gives the stated lower bound."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) => Seq(Open, a, Close, Sp, Land, Sp, Open, b, Close);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Instance(string name, params Formula[] args) =>
        Seq(OpenBracket, Call(name, args), CloseBracket, Sp);

    private static Formula LowerBound()
    {
        var vertices = V("V");
        var graph = V("G");
        var target = V("E");
        var gain = V("g");
        var epsilon = V("e");
        var reals = Seq(Mathbb, Grp(V("R")));
        var type = Seq(Mathrm, Grp(V("Type")));
        var residual = All("p", Arrow(vertices, target), Some("u", vertices, Some("v", vertices,
            And(Call("Adj", graph, V("u"), V("v")),
                Seq(D(4), Minus, epsilon, Sp, Leq, Sp, Call("Error", gain, V("p"), V("u"), V("v")))))));
        var witness = Some("E", type, Seq(
            Instance("NormedAddCommGroup", target), Instance("NormedSpace", reals, target),
            Instance("CompleteSpace", target), Instance("FiniteDimensional", reals, target),
            Some("g", Arrow(vertices, Arrow(vertices, target)),
                And(Call("Skew", vertices, gain), And(Call("Flat", graph, gain), residual)))));
        var graphs = Some("V", type, Seq(Instance("Fintype", vertices),
            Some("G", Call("SimpleGraph", vertices),
                And(Call("Chordal", graph), And(Call("Connected", graph), witness)))));
        return All("e", reals,
            new Formula.Logic(Seq(D(0), Sp, F.Lt, Sp, epsilon), FormulaLogicOperator.Implies, graphs));
    }
}
