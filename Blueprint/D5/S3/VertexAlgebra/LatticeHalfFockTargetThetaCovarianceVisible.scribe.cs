using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockTargetThetaCovarianceVisibleDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Visible original L0 covariance",
        H("Original coefficient weight covariance"),
        Blocks(Describe.Lean(
            DescribeId.Create("latticehalffocktargetthetacovariancevisible-ytw-l-zero-covariance"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockLZeroCovariance.Ytw_L0_covariance"),
            H("Visible original L0 covariance"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Background),
            Blocks(Paragraph(Text("The repaired module keeps the original coefficient field, source and target homogeneous hypotheses, and both inverse-Gram equations. Its omega step uses the visible exact Ytw_omega supplier."))),
            DescribeRole.Theorem))));
}
