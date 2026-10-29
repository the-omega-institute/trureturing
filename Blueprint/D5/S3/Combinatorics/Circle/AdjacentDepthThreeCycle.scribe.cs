using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class AdjacentDepthThreeCycleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native long seeds carry a physical order-three cycle.",
        H("Native adjacent-depth long-seed three-cycle"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("native-long-seed-three-cycle"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Circle/AdjacentDepthThreeCycle.native_long_seed_three_cycle"),
                H("Native adjacent-depth long-seed three-cycle"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("trureturing/native-adjacent-depth")),
                Blocks(
                    Paragraph(Text(
                        "For a native centered doubling source with k at least three and strictly positive SMALL labels, native_chain_extraction supplies each first-hit chain. When the selected first-hit length is h+1 with h at least one, the physical root, following negative, and next seed are distinct occurrences. Rotating their literal order from [root, negative, seed] to [seed, root, negative] is an actual order-three permutation with an explicit inverse.")),
                    Paragraph(Text(
                        "The theorem records the native root, negative, and next-label formulas and the two unsigned-potential seam identities. It does not claim the later global mixed root-only loose-run sweep, either cyclic filter order, or the full C3.1 half-strip conjecture; those remain separate obligations."))),
                DescribeRole.Theorem)))));
}
