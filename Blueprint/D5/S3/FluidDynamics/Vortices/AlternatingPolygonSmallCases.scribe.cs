using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Vortices;

internal sealed class AlternatingPolygonSmallCasesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Vortices/AlternatingPolygonSmallCases.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/FluidDynamics/barrykevrekidis2013vortex");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The dipole and square are treated separately: lambda squared times (lambda squared plus one half), and lambda squared times (lambda squared plus two) times (lambda squared plus one quarter) squared. Their exact complex roots and their unbounded real neutral drift are distinguished. The square roots are plus or minus i*sqrt(2), and twice plus or minus i/2, as proved from the actual field; these differ from BK arXiv v2 Eq. (12).",
        H("Alternating Polygon Small Cases"), Blocks(
            Paragraph(Text("The source extension is the 4 November 2026 note by Haobo Ma and Wenlin Zhang, in that order. Barry and Kevrekidis retain prior equilibrium, instability and small-spectrum credit. The original Conjecture 4.4 real-root proof and its field, rotation, Fourier and determinant suppliers are reused; no priority certification is made.")),
            Node("dipole", "dipole", "The actual dipole polynomial and its exhaustive complex spectrum.", DescribeRole.Theorem),
            Node("square", "square", "The square constants are settled by the actual Cartesian field, with no presumed explanation for the different numbers printed in BK arXiv v2 Eq. (12).", DescribeRole.Theorem),
            Node("small_neutral_drift", "small neutral drift", "Spectral neutrality coexists with a nonzero actual real unbounded drift orbit.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("alternating-polygon-small-cases-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
