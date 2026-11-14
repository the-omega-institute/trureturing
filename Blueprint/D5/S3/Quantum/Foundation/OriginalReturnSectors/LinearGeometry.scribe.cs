using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation.OriginalReturnSectors;

internal sealed class LinearGeometryDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/OriginalReturnSectors/LinearGeometry.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real singular estimates and minimum-norm geometry for the actual projected operator.",
        H("Ordered spectra and projected-kernel margins"), Blocks(
        Describe.Lean(DescribeId.Create("singular-tail"), DeclarationHandle.Create(Owner + "singularTail"),
            H("Ordered right singular tail"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For an actual real return operator L, use the pinned native orthonormal eigenbasis of L adjoint composed with L, ordered by decreasing eigenvalue. W is the span of directions with zero-based index at least k. It equals the orthogonal complement of the first k directions. Within tied eigenspaces the native basis makes a choice; every estimate uses only sorted spectral inequalities, so it remains valid at ties. The definition exists for every early dimension: when k>=d the tail is zero, without asserting that the eventual bounds already hold."))), DescribeRole.Definition),
        Paragraph(Text("The ordered native eigenbasis includes tied and zero singular values. The minimum-norm argument applies to the kernel of the supplied projected operator A, independently of the injectivity of the original return chart L. A genuine ball preimage, uniqueness in the kernel orthogonal complement and radial extension give the finite squared kernel margin; projection mass transfer then connects that kernel to the ordered singular tail. The original return geometry theorem consumes these estimates. The adapted TauCeti leaves retain their copyright, immutable revision, Apache license and pinned-mathlib retirement condition in the Lean source; they carry zero independent new-content credit.")))));
}
