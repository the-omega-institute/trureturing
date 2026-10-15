using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockConformalVisibilityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original conformal visibility suppliers",
        H("Public exact tensor and trace identities"),
        Blocks(Paragraph(Text("The module exposes the exact predecessor tensor-product multiplication, finite tensor-pair support and inverse-trace identities needed by the original conformal identification. These are visibility repairs over the protected predecessor closure, with no changed private body and no replacement carrier.")),
            Describe.Lean(
                DescribeId.Create("latticehalffockconformalvisibility-tensor-pair"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockConformalVisibility.tensorPair_eq"),
                H("Original tensor-pair ordering"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The public statement follows the original sign-dependent ordering of tensor current operators."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffockconformalvisibility-inverse-trace"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockConformalVisibility.inverse_trace"),
                H("Original inverse trace"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The inverse-Gram equation yields the exact rank trace used by the original stress correction."))),
                DescribeRole.Theorem))));
}
