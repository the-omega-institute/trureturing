using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class PrescribedDegreeParitiesDocument : IScribeDocumentDefinition
{
    private static Formula Statement()
    {
        var vertices = F.Id("V");
        var graph = F.Id("G");
        var target = F.Id("d");
        var subgraph = F.Id("H");
        var vertex = F.Id("v");
        var graphs = Call("SimpleGraph", vertices);
        var bits = Call("ZMod", D(2));
        var degreeParity = Eq(Call("DegreeModTwo", subgraph, vertex), Apply(target, vertex));
        var degrees = Bind(FormulaQuantifier.ForAll, "v", vertices, degreeParity);
        var graphExists = Bind(FormulaQuantifier.Exists, "H", graphs,
            And(Call("Subgraph", subgraph, graph), degrees));
        var total = Eq(Call("Total", target), D(0));
        var law = new Formula.Logic(graphExists, FormulaLogicOperator.Iff, total);
        var targets = Bind(FormulaQuantifier.ForAll, "d", Call("VertexLabelling", vertices, bits), law);
        var connected = new Formula.Logic(Call("Connected", graph), FormulaLogicOperator.Implies, targets);
        return Disp(Bind(FormulaQuantifier.ForAll, "V", Call("FiniteVertexType"),
            Bind(FormulaQuantifier.ForAll, "G", graphs, connected)));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Vertex degree parity prescriptions on finite connected graphs.",
        H("Prescribed degree parities"),
        Blocks(Describe.Lean(
            DescribeId.Create("exact-parity-subgraph"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/PrescribedDegreeParities.exact_parity_subgraph"),
            H("A prescribed odd-degree set has even cardinality"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("V has a Fintype instance and decidable equality, and Sym2(V) has a Fintype instance. G is a connected simple graph. VertexLabelling assigns an element of ZMod(2) to each vertex, Total sums these labels, and DegreeModTwo casts the cardinality of the neighbour set to ZMod(2). Subgraph is the edge inclusion relation on simple graphs with the same vertex type.")),
                Paragraph(Text("The handshaking identity gives the zero-sum condition. For the converse, the two endpoints of a walk are the boundary of the sum of its edges over ZMod(2), since internal incidences cancel in pairs. Taking walks to one root with coefficients given by the prescription cancels the root term because the total is zero. Select the edges with coefficient one. Their incidence vector is the prescribed degree parity."))),
            DescribeRole.Theorem))));
}
