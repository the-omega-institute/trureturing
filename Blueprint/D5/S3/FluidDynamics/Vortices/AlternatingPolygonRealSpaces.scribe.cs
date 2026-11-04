using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Vortices;

internal sealed class AlternatingPolygonRealSpacesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/FluidDynamics/barrykevrekidis2013vortex");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original real Cartesian operator embeds faithfully into its complexification. Nonzero semisimplicity descends to the real operator. The stable and unstable spaces are the spectral sums of the actual negative and positive real eigenspaces. Injectivity of these sums follows from independence of distinct eigenspaces; each sign has dimension 2*(m-2), rather than merely m-2 distinct spectral values.",
        H("Alternating Polygon Real Spaces"), Blocks(
            Paragraph(Text("The full extension is set out in the 4 November 2026 note by Haobo Ma and Wenlin Zhang, in that order. Barry and Kevrekidis retain prior credit for equilibrium, instability and the small-spectrum classification. The existing Conjecture 4.4 real-root theorem and its field, rotation, Fourier and determinant proof bodies are reused. No priority certification is made.")),
            Node("realOperator", "realOperator", "The canonical Cartesian Jacobian acts on the original real displacement space.", DescribeRole.Definition),
            Node("complexify", "complexify", "The faithful real inclusion into the actual complexified Cartesian space.", DescribeRole.Definition),
            Node("complexify_injective", "complexify injective", "The coordinatewise real inclusion into the complex displacement space is injective.", DescribeRole.Theorem),
            Node("complexify_operator", "complexify operator", "The real inclusion intertwines the original real Jacobian and its actual complexification.", DescribeRole.Theorem),
            Node("real_nonzero_semisimple", "real nonzero semisimple", "Nonzero semisimplicity also holds over the original real displacement space.", DescribeRole.Theorem),
            Node("real_geometric_multiplicity", "real geometric multiplicity", "Every signed real root has a two-dimensional real eigenspace.", DescribeRole.Theorem),
            Node("spectralSum", "spectralSum", "The ordinary spectral sum for one sign; each summand is an actual real eigenspace.", DescribeRole.Definition),
            Node("unstableSpace", "unstableSpace", "The positive real spectral space is the range of the sum of actual positive eigenspaces.", DescribeRole.Definition),
            Node("stableSpace", "stableSpace", "The negative real spectral space is the range of the sum of actual negative eigenspaces.", DescribeRole.Definition),
            Node("unstable_finrank", "unstable finrank", "For m at least three the actual positive real spectral space has dimension 2*(m-2).", DescribeRole.Theorem),
            Node("stable_finrank", "stable finrank", "For m at least three the actual negative real spectral space has dimension 2*(m-2).", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("alternating-polygon-real-spaces-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
