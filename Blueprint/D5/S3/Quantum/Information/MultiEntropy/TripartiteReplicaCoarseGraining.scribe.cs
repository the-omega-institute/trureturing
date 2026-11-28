using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.MultiEntropy;

internal sealed class TripartiteReplicaCoarseGrainingDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/MultiEntropy/TripartiteReplicaCoarseGraining.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/gaddejainkrishnakulkarnisharma2024multientropy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coarse graining of finite tripartite Rényi replica moments.",
        H("Tripartite replica coarse graining"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("absolute-replica-moment-bound"),
                DeclarationHandle.Create(Module + "E_abs_coarseGraining_all_mergers"),
                H("Absolute replica moment bound for each merger"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The original tripartite contraction is the trace of a power of a row "
                    + "transfer matrix. A rectangular Gram factorization expresses the transfer "
                    + "matrix as a compression of a replica permutation. Schatten Hölder "
                    + "bounds the absolute moment by the corresponding grouped bipartite "
                    + "moment raised to the replica order. Replica relabeling gives every merger."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-replica-renyi-bound"),
                DeclarationHandle.Create(Module + "renyi_coarseGraining_all_mergers_of_positive"),
                H("Rényi entropies on the positive-moment domain"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "When the tripartite moment is positive, the logarithmic Rényi "
                    + "multi-entropy is at least the Rényi entropy of each bipartite merger."))),
                DescribeRole.Theorem))));
}
