using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class TernaryPartitionOrbitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/TernaryPartitionOrbit.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/akella2026genuine");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Opposite nonzero ternary modes give distinct anchored equality partitions, for any index type and any choice of opposite-pair representatives.",
        H("Ternary mode orbits and partition counting"),
        Blocks(
            Paragraph(Text("Akella, Iizuka and Miyata, arXiv:2607.06050v2, Section 6, ask whether a counting argument analogous to their n=2 Coxeter argument exists at n=3. This source-level question is OPEN here. The theorem below isolates the orbit classification needed by a partition-counting argument; it does not identify a Coxeter group or settle the full question.")),
            Describe.Lean(DescribeId.Create("same-partition"), DeclarationHandle.Create(Prefix + "SamePartition"),
                H("Equality of induced partitions"), StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Two colourings have the same partition when every pair of indices has equal colours in one colouring exactly when it has equal colours in the other. The index type may be infinite or empty."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("anchored-colouring"), DeclarationHandle.Create(Prefix + "anchored"),
                H("Fixing an additional colour at zero"), StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("anchored(u) assigns zero to none and assigns u(i) to some(i). A nonzero u therefore produces a nonconstant anchored colouring, including when some of its entries are zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("partition-orbit-representatives"), DeclarationHandle.Create(Prefix + "result"),
                H("Opposite-pair representatives classify every anchored ternary partition"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The representative set P may be any set of ternary modes that contains exactly one of u and -u for each nonzero u. For every nonzero mode u there is exactly one member v of P with the same anchored equality partition. These are partitions with two or three blocks that are realized by anchored ternary colourings; the all-constant partition and partitions with four or more blocks are outside the conclusion. No finiteness or choice of coordinates is assumed. The proof first constructs the unique affine permutation between nonconstant ternary colourings with the same equality partition: two distinct colours determine the slope and intercept, and a third distinct colour is minus the other two. Fixing the anchor at zero forces the intercept to vanish, so the only remaining slopes are 1 and -1."))), DescribeRole.Theorem),
            H("The thirteen four-party patterns"),
            Paragraph(Text("For three free coordinates and the fourth party anchored at zero, select the first nonzero coordinate to be 1. The 26 nonzero ternary modes form thirteen opposite pairs, giving the thirteen modes listed below. Their partitions have two or three blocks; the one-block and four-block partitions do not occur. The theorem explains why these rows are distinct partition patterns. A merger contributes exactly when its two labels lie in the same block; the number of such mergers is the sum of choose(block size,2).")),
            Paragraph(Text("mode 001: ABD:C; 3 compatible pair mergers; signed coefficient 1-3+2=0.")),
            Paragraph(Text("mode 010: ACD:B; 3 compatible pair mergers; signed coefficient 1-3+2=0.")),
            Paragraph(Text("mode 011: AD:BC; 2 compatible pair mergers; signed coefficient 1-2+1=0.")),
            Paragraph(Text("mode 012: AD:B:C; 1 compatible pair merger; signed coefficient 1-1=0.")),
            Paragraph(Text("mode 100: A:BCD; 3 compatible pair mergers; signed coefficient 1-3+2=0.")),
            Paragraph(Text("mode 101: AC:BD; 2 compatible pair mergers; signed coefficient 1-2+1=0.")),
            Paragraph(Text("mode 102: A:BD:C; 1 compatible pair merger; signed coefficient 1-1=0.")),
            Paragraph(Text("mode 110: AB:CD; 2 compatible pair mergers; signed coefficient 1-2+1=0.")),
            Paragraph(Text("mode 111: ABC:D; 3 compatible pair mergers; signed coefficient 1-3+2=0.")),
            Paragraph(Text("mode 112: AB:C:D; 1 compatible pair merger; signed coefficient 1-1=0.")),
            Paragraph(Text("mode 120: A:B:CD; 1 compatible pair merger; signed coefficient 1-1=0.")),
            Paragraph(Text("mode 121: AC:B:D; 1 compatible pair merger; signed coefficient 1-1=0.")),
            Paragraph(Text("mode 122: A:BC:D; 1 compatible pair merger; signed coefficient 1-1=0.")),
            Paragraph(Text("Thus the 2+1+1 patterns cancel against one merger, the 2+2 patterns require one bipartite correction, and the 3+1 patterns require twice the singleton-cut correction. Multiplying each row by an arbitrary coefficient f of its equality partition yields the signed-incidence relation used by StabilizerMultiEntropyCollapse.partition_count. This is a structural interpretation of that existing exact identity; this module adds no finite enumeration theorem and no new entropy-collapse claim.")))));
}
