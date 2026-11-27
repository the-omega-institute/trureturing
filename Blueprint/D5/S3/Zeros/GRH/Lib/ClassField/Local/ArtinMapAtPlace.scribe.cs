using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.Local;

internal sealed class ArtinMapAtPlaceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Artin Map At Place", H("Artin Map At Place"),
        Blocks(
            Paragraph(Text("Local Artin map: norm functoriality, density, units to inertia, tame symbol, tame generator.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/Local/ArtinMapAtPlace.exists_localArtin_eq_tameGenerator"),
                H("exists_localArtin_eq_tameGenerator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For A above w, there is a unit u of K_w whose local Artin image is the class of the chosen tame generator of inertia and whose residue generates the multiplicative group of the residue field.")))))));
}
