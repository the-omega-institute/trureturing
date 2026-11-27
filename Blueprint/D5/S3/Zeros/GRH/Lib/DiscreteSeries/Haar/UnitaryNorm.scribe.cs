using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Haar;

internal sealed class UnitaryNormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unitary Norm", H("Unitary Norm"),
        Blocks(
            Paragraph(Text("Hermitian involutions and real coordinates on skew-hermitian matrices. Operator norm and determinant of elements of U(p,q).")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Haar/UnitaryNorm.skewCoords"),
                H("skewCoords"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The real linear map sending a complex matrix x to the real matrix with entries Re x_ab + Im x_ab, divided by √2 off the diagonal; a left inverse of skewOfReal.")))))));
}
