using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Haar;

internal sealed class SkewCoordinatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Skew Coordinates", H("Skew Coordinates"),
        Blocks(
            Paragraph(Text("Real determinant of two-sided multiplication; basic API for U(J) and skew coordinates.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Haar/SkewCoordinates.det_mulLeft_mulRight_real"),
                H("det_mulLeft_mulRight_real"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For complex square matrices P of size m and Q of size n, the real-linear map X ↦ PXQ on complex m×n matrices has determinant |det P|^(2n)·|det Q|^(2m).")))))));
}
