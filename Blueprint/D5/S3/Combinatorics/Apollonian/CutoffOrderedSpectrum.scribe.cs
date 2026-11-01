using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Apollonian;
internal sealed class CutoffOrderedSpectrumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Apollonian/CutoffOrderedSpectrum.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Eigenstructure/radsararanando2026apollonian");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered spectra of the actual old-to-late graph block.", H("Actual cutoff dilation spectrum"), Blocks(
            Node("cutoffDilation", "The actual cutoff dilation", "For natural k,t, the real matrix cutoffDilation k t acts on Vertex k plus LateVertex k t and has blocks [[0,B],[transpose B,0]], where B is the actual zero-one cutoff adjacency block. The two diagonal blocks are zero and the vertex types may have unequal cardinalities.", DescribeRole.Definition),
            Node("cutoffSecond", "The second decreasing dilation eigenvalue", "For natural k,t, cutoffSecond k t is index one in the decreasing real Hermitian spectrum of cutoffDilation k t, with algebraic multiplicity. The four persistent seed vertices ensure this index exists.", DescribeRole.Definition),
            Node("cutoff_second_eq_sqrt_gram", "The actual positive second-spectrum bridge", "For every natural k,t, if the second decreasing eigenvalue of the actual Gram matrix B B^T on Vertex k is strictly positive, then cutoffSecond k t is its positive square root. No equality of the old and late block sizes is assumed. Characteristic-polynomial zero padding and real-to-complex embedding retain the ordered positive prefix, signs and algebraic multiplicities. The positivity premise remains explicit; this conditional identity does not establish the original all-stage adjacency limit.", DescribeRole.Theorem))));
    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("apollonian-ordered-" + name.ToLowerInvariant().Replace("_", "-")),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
