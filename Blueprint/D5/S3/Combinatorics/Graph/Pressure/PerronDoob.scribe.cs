using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Pressure;
internal sealed class PerronDoobDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual exponential transfer matrix and Doob stationary law", H("Actual exponential transfer matrix and Doob stationary law"), Blocks(
        Paragraph(Text("The notation FiniteDecidableType means an arbitrary finite type with decidable equality; RealEdgeCosts(X) means an arbitrary function X -> X -> Real. Let X be finite and let G be a Prop-valued directed support. G.connected connects every ordered vertex pair by an ordinary, possibly empty path, and G.hasEdge supplies an actual edge. This includes every original loopless simple strongly connected graph with an edge; loops are also permitted by this stronger formulation. Costs c are arbitrary real functions. W is exactly exp(-c/temperature) on G.edge and zero elsewhere. No row normalization or aperiodicity is assumed.")),
        Describe.Lean(DescribeId.Create("actual-graph-result"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Pressure/PerronDoob.exists_perron"),
            H("Actual exponential transfer matrix and Doob stationary law"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                "D5/L/GraphInvariants/friedlandgaubert2019spectral")),
            Blocks(Paragraph(Text("Transport original paths along the exact positive support and use the existing positive-path connectivity lemma. Apply the source-equivalent MCMC supplier to this actual matrix, then transport its real positive eigenvector to the complex matrix. Spectrum membership and the supplier eigenvalue-modulus bound give both inequalities for the extended nonnegative complex spectral radius. Define Qstar as W(i,j)r(j)/(root*r(i)); positivity gives exact original support, and the eigenrelation gives row sum one. Apply the existing finite stationary-distribution supplier to Qstar itself."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Family(Formula body) => All("X", Call("FiniteDecidableType"),All("G", Call("Network",F.Id("X")),
        All("c",Call("RealEdgeCosts",F.Id("X")),All("temperature",Call("Real"),body))));
    private static Formula Statement() => Family(Call("Nonempty",Call("Perron",F.Id("G"),F.Id("c"),F.Id("temperature"))));
}
