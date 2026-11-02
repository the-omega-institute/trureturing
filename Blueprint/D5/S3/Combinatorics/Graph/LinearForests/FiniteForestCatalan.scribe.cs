using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LinearForests;

internal sealed class FiniteForestCatalanDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/LinearForests/FiniteForestCatalan.";
    private static Formula Name(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The alternating Catalan sum over all actual independent subsets of every finite acyclic graph of maximum degree two is nonnegative at every parameter at least its full vertex count.",
        H("The Catalan functional on finite linear forests"),
        Blocks(
            Describe.Lean(DescribeId.Create("forest-nonnegative"),
                DeclarationHandle.Create(Prefix + "finite_forest_phi_nonnegative"),
                H("All vertices and all legal parameters"),
                StatementSource.FromAuthor(Disp(
                    All("V", Name("Type"),
                        Imp(And(Call("Fintype", F.Id("V")), Call("DecidableEq", F.Id("V"))),
                            All("G", Call("SimpleGraph", F.Id("V")),
                                Imp(Call("DecidableRel", Call("Adj", F.Id("G"))),
                                    All("m", Name("Nat"),
                                        Imp(And(Call("IsAcyclic", F.Id("G")),
                                                And(All("v", F.Id("V"), Le(Call("degree", F.Id("G"), F.Id("v")), D(2))),
                                                    Le(Call("card", F.Id("V")), F.Id("m")))),
                                            Le(D(0), Call("phi", F.Id("G"), Call("univ", F.Id("V")), F.Id("m"))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let V be any finite vertex type with decidable equality, and let G be any simple graph on V with decidable adjacency. Assume that G is acyclic and that every vertex has degree at most two. For every natural m at least the cardinality of V, the integer phi(G,univ,m) is nonnegative. Here phi is PathCatalanFunctional.phi: it sums (-1) to card(S) times Catalan(m-card(S)) over all actual independent subsets S of the full vertex set. Empty graphs, arbitrary isolated vertices, arbitrarily many components and the boundary m=card(V) are included.")),
                    Paragraph(Text("A longest simple path in a connected component contains every vertex. An edge leaving an endpoint would extend it; an edge leaving an interior vertex would give three distinct neighbors. The Hamiltonian vertex enumeration identifies the path graph with a spanning subgraph, and maximal acyclicity excludes additional edges. Induction over the remaining actual vertices concatenates these component enumerations into a bijection from the full vertex type to a finite interval, carrying every original edge to consecutive indices.")),
                    Paragraph(Text("For two distinct nonadjacent vertices u and v in a finite domain W, write N_u and N_v for the respective closed-neighborhood complements within W. The independent-partition deletion identity, applied at u and then at v inside N_u, gives P_G=P_(G+uv)+w(u)w(v)P_(G on N_u intersect N_v). The added edge does not change adjacency on a domain omitting an endpoint. With each activity equal to -X, multiply by the integer Catalan series and take coefficient m. When m is at least card(W), this yields phi(G,W,m)=phi(G+uv,W,m)+phi(G,N_u intersect N_v,m-2). The residual domain has at most card(W)-2 vertices.")),
                    Paragraph(Text("Induct first on the full actual vertex count and then on the number of missing edges in the spanning path. The added-edge term reduces the missing-edge count; the residual term is an actual induced forest on fewer vertices and has a legal shifted parameter. At the complete path, the configuration-preserving vertex bijection transports the functional directly to PathCatalanFunctional.path_phi_nonnegative. Its path recurrence and generating-series identity are reused through that theorem."))),
                DescribeRole.Theorem)), []));
}
