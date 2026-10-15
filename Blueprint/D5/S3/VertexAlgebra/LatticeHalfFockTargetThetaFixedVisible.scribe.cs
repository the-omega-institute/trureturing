using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockTargetThetaFixedVisibleDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Visible theta-fixed restriction",
        H("Original theta-fixed odd-target restriction"),
        Blocks(Describe.Lean(
            DescribeId.Create("latticehalffocktargetthetafixedvisible-ytw-fixed-odd-target"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockTargetThetaFixed.Ytw_fixed_oddTarget"),
            H("Original theta-fixed odd-target restriction"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Background),
            Blocks(Paragraph(Text("Theta-fixed sources preserve the actual odd target ker(S+id). The restricted cover retains the original vacuum and even-mode vanishing, while the physical coefficient records the literal -2n-2 exponent and the k+r-n-1 weight shift."))),
            DescribeRole.Theorem))));
}
