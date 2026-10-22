using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockTargetThetaCorrectionWeightDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original finite correction Euler supplier binding",
        H("Original finite correction Euler supplier binding"),
        Blocks(Describe.Lean(
            DescribeId.Create("latticehalffocktargetthetacorrectionweight-Corr-Euler"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockTargetThetaCorrectionWeight.Corr_Euler"),
            H("Original finite correction Euler supplier binding"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Background),
            Blocks(Paragraph(Text("The exact completed source proof body is retained in this consumed module. Checked private aliases repair visibility without changing any protected predecessor. This is supplier reuse, not a second claim of new mathematics. Both inverse-Gram equations remain explicit whenever present. The full original goal and the independent spectral classification remain outside this statement."))),
            DescribeRole.Theorem))));
}
