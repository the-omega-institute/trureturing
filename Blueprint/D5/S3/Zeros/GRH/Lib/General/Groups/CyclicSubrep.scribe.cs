using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Groups;

internal sealed class CyclicSubrepDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cyclic Subrep", H("Cyclic Subrep"),
        Blocks(
            Paragraph(Text("Cyclic subrepresentation of a vector; subrepresentation of smooth vectors.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Groups/CyclicSubrep.smoothVectorRep"),
                H("smoothVectorRep"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The subrepresentation of ρ on its smooth vectors, those fixed by all g in some neighbourhood of 1.")))))));
}
