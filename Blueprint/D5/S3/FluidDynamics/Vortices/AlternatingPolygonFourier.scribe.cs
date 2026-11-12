using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Vortices;

internal sealed class AlternatingPolygonFourierDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Vortices/AlternatingPolygonFourier.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/FluidDynamics/barrykevrekidis2013vortex");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coordinate map is an actual linear equivalence: first faithfully relabel the polygon, then use the canonical DFT, and shift the tangential frequency by m. Its action is derived from the existing circulant and inverse-chord transform proofs. No eigenvalue list is assumed.",
        H("Alternating Polygon Fourier"), Blocks(
            Paragraph(Text("The full extension is set out in the 4 November 2026 note by Haobo Ma and Wenlin Zhang, in that order. Barry and Kevrekidis retain prior credit for equilibrium, instability and the small-spectrum classification. The existing Conjecture 4.4 real-root theorem and its field, rotation, Fourier and determinant proof bodies are reused. No priority certification is made.")),
            Node("relabel", "relabel", "Relabel the existing finite polygon, without changing its cyclic order.", DescribeRole.Definition),
            Node("fourier", "fourier", "The canonical DFT, after the faithful cyclic relabeling.", DescribeRole.Definition),
            Node("frequencyCoordinates", "frequencyCoordinates", "Paired Fourier coordinates. The tangential frequency is shifted by m.", DescribeRole.Definition),
            Node("frequency_block", "frequency block", "The actual radial/tangential block action in the complete Fourier coordinates.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("alternating-polygon-fourier-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
