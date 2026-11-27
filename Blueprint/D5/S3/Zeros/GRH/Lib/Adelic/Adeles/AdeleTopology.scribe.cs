using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Adeles;

internal sealed class AdeleTopologyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adele Topology", H("Adele Topology"),
        Blocks(
            Paragraph(Text("Topology of completions and finite adeles: local compactness, density of field, conjugation.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Adeles/AdeleTopology.exists_dvd_sub_algebraMap"),
                H("exists_dvd_sub_algebraMap"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a nonzero a in O_E, every integral finite adele x in Ô is congruent modulo aÔ to an element of O_E (Chinese remainder theorem).")))))));
}
