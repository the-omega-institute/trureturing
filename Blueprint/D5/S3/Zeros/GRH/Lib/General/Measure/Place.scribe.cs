using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Measure;

internal sealed class PlaceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Place", H("Place"),
        Blocks(
            Paragraph(Text("Leray measures on hermitian quadrics disintegrate volume, uniquely, over an axiomatised place (Place).")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Measure/Place.isDisintegration_quadricMeasure"),
                H("isDisintegration_quadricMeasure"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For T hermitian, the flat chart measures δ_Γ form a disintegration of the volume along h(v, v), for the form made of a hyperbolic pair and T.")))))));
}
