using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum;

internal sealed class GradingDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite native homogeneous reconstruction",
        H("Natural occupation-weight projectors"),
        Blocks(
            Paragraph(Text("The projector at N filters the actual ground-valued occupation coefficients by W(d)=N and applies the inverse tensor-monomial equivalence. It is a linear endomorphism of the complete original carrier. The finite set supportedLevels is the image of the actual coefficient support under W, not a prescribed list of allowed occupations.")),
            Describe.Lean(
                DescribeId.Create("native-half-fock-finite-reconstruction"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockNativeSpectrum/Grading.finite_reconstruction"),
                H("Exact reconstruction of every original state"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("Every state equals the sum of its natural projectors over supportedLevels. In each occupation coordinate exactly its own weight contributes. Coordinates outside the support vanish. Thus reconstruction is finite on every state without any uniform occupation bound."))),
                DescribeRole.Theorem),
            Paragraph(Text("Under both Gram inverse equations, projector_eigen places each component in the original eigenspace of rank/16+N/2. weightValue is injective. projector_on_eigen recovers the selected component and kills every other one, projector_composition gives orthogonality, and finite_directness proves that a finite sum of distinct homogeneous states is zero only when each summand is zero.")),
            Paragraph(Text("This is an algebraic finite-support decomposition. It makes no assertion about Hilbert completion, convergence of infinite sums, realized conformal field theories or orbifold extensions.")))));
}
