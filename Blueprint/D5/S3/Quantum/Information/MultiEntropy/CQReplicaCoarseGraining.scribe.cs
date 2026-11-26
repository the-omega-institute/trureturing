using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.MultiEntropy;

internal sealed class CQReplicaCoarseGrainingDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/gaddejainkrishnakulkarnisharma2024multientropy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A classical–quantum marginal gives a positive tripartite replica moment and all three coarse-graining inequalities.",
        H("Tripartite Rényi multi-entropy for classical–quantum marginals"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("classical-quantum-replica-trace"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/MultiEntropy/CQReplicaCoarseGraining."
                    + "E_eq_trace_tensor_sum_pow"),
                H("Trace formula for the tripartite moment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The tripartite contraction is the trace of the n-th power of the sum "
                    + "of the n-fold tensor powers of the classical–quantum blocks. The "
                    + "classical labels are constant on each cycle of the first replica "
                    + "translation. The second replica translation gives ordered traces "
                    + "of products of the quantum blocks, which may fail to commute."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("classical-quantum-replica-coarse-graining"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/MultiEntropy/CQReplicaCoarseGraining."
                    + "E_coarseGraining_all_mergers"),
                H("All three ways to merge two parties"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Let A, B and C have finite bases, let the pure state be normalized, and let "
                    + "the AB marginal be block diagonal along A. The positive quantum blocks "
                    + "may fail to commute. At every integer replica order n ≥ 2, the tripartite "
                    + "moment is real and strictly positive. It is bounded above by the n-th "
                    + "power of the bipartite replica moment after each of the mergers AB, AC "
                    + "and BC. These are the raw moment inequalities of Gadde et al., "
                    + "arXiv:2308.16247, equation (1.13), in this state class. "
                    + "Tasuki, arXiv:2611.34715v1, §2.3, discusses the all-state result at n=2 "
                    + "and the continuum vacuum case. The proof expresses the finite tripartite "
                    + "moment as the trace of a power of a positive sum of tensor powers. "
                    + "The three bounds use the Schatten triangle inequality, the scalar "
                    + "power-sum inequality and monotonicity under positive semidefinite order."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("classical-quantum-renyi-coarse-graining"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/MultiEntropy/CQReplicaCoarseGraining."
                    + "renyi_coarseGraining_all_mergers"),
                H("Rényi entropy after merging parties"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The merged bipartite moments are strictly positive. Taking real logarithms "
                    + "with the normalization of equation (1.11) bounds each merged bipartite "
                    + "Rényi entropy above by the tripartite Rényi multi-entropy, for the same "
                    + "finite classical–quantum marginal and replica orders."))),
                DescribeRole.Theorem))));
}
