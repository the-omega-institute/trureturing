using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.AbelianScheme;

internal sealed class SpecialisationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Specialisation", H("Specialisation"),
        Blocks(
            Paragraph(Text("Geometric points in locally closed sets; homogeneity and dimension of group schemes. Properties at geometric specialisations; flat maps are injective on stalks.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/AbelianScheme/Specialisation.smoothOfRelativeDimension_of_fibres"),
                H("smoothOfRelativeDimension_of_fibres"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let A be an abelian scheme over S with dense complex points y_i over η_i. If g is the only possible relative dimension of each fibre over η_i, then A is smooth of relative dimension g over S.")))))));
}
