using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class CycleFiveStrongOneResistanceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/CycleFiveStrongOneResistance.";
    private static readonly LibraryNoteRef Han = LibraryNoteRef.Create("D5/L/QuantumStates/han2026resistant");
    private static readonly LibraryNoteRef Zhang = LibraryNoteRef.Create("D5/L/QuantumStates/zhang2025resistant");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The five-cycle graph state is genuinely multipartite entangled, remains genuinely multipartite entangled after any one-qubit loss, and becomes fully separable after any two-qubit loss.",
        H("The five-cycle graph state is strongly 1-resistant"),
        Blocks(
            Describe.Lean(DescribeId.Create("cycle-five-claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("The C5 clause of the published question"),
                StatementSource.FromAuthor(Disp(new Formula.Relation(F.Id("claim"), FormulaRelationOperator.Equal,
                    Call("IsStrongResistant", D(1), Call("cycleGraphState", D(5)))))),
                AssessedProvenance.FromLiterature(Han),
                Blocks(Paragraph(Text("Han, Zhang and Zhang, arXiv:2606.08561v1, page 8, Discussion: \"Several open problems remain. First, do C₅ and C₆ give strongly m-resistant graph states for m = 1 and m = 2, respectively? Here, “strong” means genuine multipartite entanglement rather than mere entanglement.\" This claim is the C5, m = 1 clause. The imported cycleGraphState labels qubits by Fin 5, numbered 0,...,4, with amplitudes (-1) raised to the cyclic sum of adjacent bit products, divided by sqrt(32). The imported strong-resistance predicate requires initial genuine multipartite entanglement, genuine multipartite entanglement of every one-qubit-loss marginal, and full separability of every two-qubit-loss marginal. GME excludes finite convex mixtures of products across arbitrary nontrivial bipartitions, including mixtures whose cuts differ between terms. Full separability is a finite convex mixture of products of single-qubit positive semidefinite trace-one density matrices."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cycle-five-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Strong 1-resistance of the five-cycle state"),
                StatementSource.FromAuthor(Disp(F.Id("claim"))),
                AssessedProvenance.FromRepo(Han, Zhang),
                Blocks(Paragraph(Text("For the initial density matrix rho5 use W = I/2 - rho5; for each four-qubit marginal rho4 use W = I/2 - 2 rho4. In every case the expectation is -1/2, and the partial transpose of W is positive semidefinite across every nontrivial cut. Exact nonnegative graph-basis Gram decompositions establish this positivity. Reindexing the trace pairing shows that these witnesses have nonnegative expectation on each cut-product density matrix and hence on every biseparable mixture, so their negative expectation proves genuine multipartite entanglement. The finite checks include all 30 oriented cuts on five qubits and all 14 oriented cuts for each of the five four-qubit marginals. For each of the ten two-qubit loss sets, the three-qubit marginal is an equal mixture of four product states chosen from local Pauli eigenstates; the four weights are 1/4. All three clauses of strong resistance follow."))),
                DescribeRole.Theorem)), []));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
}
