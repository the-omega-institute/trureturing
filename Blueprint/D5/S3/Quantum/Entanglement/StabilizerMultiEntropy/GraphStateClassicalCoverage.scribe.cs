using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy;

internal sealed class GraphStateClassicalCoverageDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphStateClassicalCoverage.";
    private static readonly LibraryNoteRef Gce =
        LibraryNoteRef.Create("D5/L/QuantumStates/liu2025generalized");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Graph-state generalized concentratable entanglement has a universal classical hit-probability representation exactly at integer orders above one.",
        H("Integer orders and exact graph-state classical coverage"),
        Blocks(
            Describe.Lean(DescribeId.Create("graph-state-classical-coverage-iff"),
                DeclarationHandle.Create(Owner + "physical_graph_coverage_iff"),
                H("Universal classical hit law iff integer order"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(Gce),
                Blocks(
                    Paragraph(Text("A graph is any symmetric binary adjacency matrix with zero diagonal, including the graph on zero sites. "
                        + "The deficiency D(K,A,S) is one minus the arithmetic mean of the actual real power traces over the subsets of S, "
                        + "using the normalized reduced graph-state matrices. Equivalently it is (K - 1) times the GCE of S. "
                        + "A law p is nonnegative and normalized on binary words; Hit(S,p) is its mass on words nonzero on some site of S. "
                        + "One and the same law must work for all subsets S of the chosen graph.")),
                    Paragraph(Text("At order n + 1, sample n independent induced vertex subsets uniformly, form each induced graph's odd-degree set, "
                        + "and XOR those sets. Its exact linear-cut Fourier moments give the desired law. For a noninteger order, "
                        + "a binary projective incidence graph makes a signed marginal negative through the exact projective rank product. "
                        + "The theorem concerns universality over graph states. It does not say that every graph at a noninteger order fails."))),
                DescribeRole.Theorem))));

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula domain, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), domain, body);
    private static Formula All(string name, Formula domain, Formula body) =>
        Bind(FormulaQuantifier.ForAll, name, domain, body);
    private static Formula Ex(string name, Formula domain, Formula body) =>
        Bind(FormulaQuantifier.Exists, name, domain, body);
    private static Formula P(Formula f) => Seq(Open, f, Close);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(P(a), FormulaLogicOperator.Implies, P(b));

    private static Formula Statement()
    {
        var k = F.Id("K");
        var n = F.Id("n");
        var N = F.Id("N");
        var a = F.Id("A");
        var S = F.Id("S");
        var p = F.Id("p");
        var nat = Seq(Mathbb, Grp(F.Id("N")));
        var sites = Call("Fin", N);
        var laws = All("N", nat, All("A", Call("SimpleBinaryAdjacency", sites),
            Ex("p", Call("ProbabilityOnBinaryWords", sites),
                All("S", Call("Subsets", sites), Equal(Call("D", k, a, S), Call("Hit", S, p))))));
        var integer = Ex("n", nat, Equal(k, new Formula.Binary(n, FormulaBinaryOperator.Add, Num(1))));
        var iff = new Formula.Logic(P(laws), FormulaLogicOperator.Iff, P(integer));
        return Disp(All("K", Seq(Mathbb, Grp(F.Id("R"))), Implies(
            new Formula.Relation(Num(1), FormulaRelationOperator.LessThan, k), iff)));
    }
}
