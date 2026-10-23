using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class TernaryPartitionOrbitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/TernaryPartitionOrbit.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/akella2026genuine");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonzero ternary modes modulo sign are classified by their anchored equality partitions, for any index type and any choice of opposite-pair representatives.",
        H("Ternary mode orbits and partition counting"),
        Blocks(
            Paragraph(Text("Akella, Iizuka and Miyata, arXiv:2607.06050v2, Section 6, ask whether a counting argument analogous to their n=2 Coxeter argument exists at n=3. The theorem below is consumed by TernaryPartitionCounting, whose generic merger transport and arbitrary-weight result feed the structural partition-counting proof in StabilizerMultiEntropyCollapse for the n=3 four-party relation. Surjective mergers induce quotient colourings, normalization at the chosen target anchor removes translation, and representative selection transports arbitrary weighted sums. This does not identify a Coxeter group or settle other party or replica counts.")),
            Paragraph(Text("Akella and Gadde, Rényi multi-entropy of graph states and the n → 1 limit, arXiv:2610.27080v1 (19 October 2026), Section II Eqs. (7)–(9) and Appendix A, prove an odd-replica rank formula whose n=3 specialization also implies the four-party collapse. At n=3 the three nonzero F₄ labels give an invertible diagonal rescaling to the equality-partition separation matrix. Restoring the factor n^{−(q−2)} explicitly omitted in their Eq. (2) gives the normalization used here. This delivery supplies a structural formal proof and reusable partition library for an existing conclusion; it makes no new unique-solve or global-priority claim. The Section 6 quotation above records the source-text question, not a current certification that no other proof exists.")),
            Describe.Lean(DescribeId.Create("same-partition"), DeclarationHandle.Create(Prefix + "SamePartition"),
                H("Equality of induced partitions"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Two colourings have the same partition when every pair of indices has equal colours in one colouring exactly when it has equal colours in the other. The index type may be infinite or empty."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("anchored-colouring"), DeclarationHandle.Create(Prefix + "anchored"),
                H("Fixing an additional colour at zero"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("anchored(u) assigns zero to none and assigns u(i) to some(i). A nonzero u therefore produces a nonconstant anchored colouring, including when some of its entries are zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("partition-orbit-representatives"), DeclarationHandle.Create(Prefix + "result"),
                H("Opposite-pair representatives classify every anchored ternary partition"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The representative set P may be any set of ternary modes that contains exactly one of u and -u for each nonzero u. For every nonzero mode u there is exactly one member v of P with the same anchored equality partition. These are partitions with two or three blocks that are realized by anchored ternary colourings; the all-constant partition and partitions with four or more blocks are outside the conclusion. No finiteness or choice of coordinates is assumed. The proof first constructs the unique affine permutation between nonconstant ternary colourings with the same equality partition: two distinct colours determine the slope and intercept, and a third distinct colour is minus the other two. Fixing the anchor at zero forces the intercept to vanish, so the only remaining slopes are 1 and -1."))), DescribeRole.Theorem),
            new DocumentBlock.Section(H("The thirteen four-party patterns"), Blocks(
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
            Paragraph(Text("Thus the 2+1+1 patterns cancel against one merger, the 2+2 patterns require one bipartite correction, and the 3+1 patterns require twice the singleton-cut correction. Multiplying each row by an arbitrary coefficient f of its equality partition yields the signed-incidence relation used by StabilizerMultiEntropyCollapse.partition_count. The production partition_count proof now uses the orbit theorem through a merger-to-partition bijection and a finite partition-coefficient cancellation, rather than only interpreting the existing identity. This foundation module adds no independent finite enumeration theorem or new entropy-collapse statement.")))))));
}
