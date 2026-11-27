using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.WoodsHole;

internal sealed class IsolatedCoincidencesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Isolated Coincidences", H("Isolated Coincidences"),
        Blocks(
            Paragraph(Text("Reduced coincidences of two maps are finitely many; local Jacobian terms.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/WoodsHole/IsolatedCoincidences.hasJacobianRatio"),
                H("hasJacobianRatio"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let W have an atlas of dimension d and P be a tangent polynomial of c, u at w with P(1) ≠ 0. Then HasJacobianRatio holds at w with determinant P(t)/P(1) for all t, and every k[ε]-valued coincidence above w is constant.")))))));
}
