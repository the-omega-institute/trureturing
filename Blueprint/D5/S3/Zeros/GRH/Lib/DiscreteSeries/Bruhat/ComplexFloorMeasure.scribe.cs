using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Bruhat;

internal sealed class ComplexFloorMeasureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complex Floor Measure", H("Complex Floor Measure"),
        Blocks(
            Paragraph(Text("Product of Heisenberg floor measures equals coordinate Haar measure on the unipotent group.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Bruhat/ComplexFloorMeasure.ascConv_heisenbergMeasure_eq_besselHaar"),
                H("ascConv_heisenbergMeasure_eq_besselHaar"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The measure Shape.besselHaar on 𝖴, viewed on G₁, equals the convolution η₀∗⋯∗η_{ϱ−1} of the measures of the floors.")))))));
}
