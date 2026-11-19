using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class HeawoodMatrixActionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conjugating the Fano flag gain transports the actual two-sheet graph.",
        H("Coordinate transport of Heawood double covers"), Blocks(
        Describe.Lean(DescribeId.Create("isomorphic-of-phi-conjugate"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/StarForming/HeawoodMatrixAction.isomorphic_of_phi_conjugate"),
            H("Conjugate gains give isomorphic double covers"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source), Blocks(
                Paragraph(Text("Let s and t be signings of the twenty-one flags of the binary Fano plane. If the linear gain of t equals g times the gain of s times the inverse of g for an invertible binary three-by-three matrix g, the two-sheet graphs of s and t are isomorphic.")),
                Paragraph(Text("The matrix acts on nonzero point columns and its inverse acts on nonzero line rows. Their pairing is invariant, so the resulting permutation acts on flags. Under the same permutation, each point-line outer product is conjugated by g and the corresponding signing weight travels with the flag. The graph relabeling keeps the sheet coordinate. The equal-gain switching theorem transports the resulting signing to t."))),
            DescribeRole.Theorem),
        Paragraph(Text("Source: Heawood double-cover gain, linear conjugacy. https://github.com/the-omega-institute/subquorum-colorings/blob/48728b42d39ab3de5de251c61da5a404ec418a69/docs/HEAWOOD_DOUBLE_COVER_GAIN.md#L26-L108")))));
}
