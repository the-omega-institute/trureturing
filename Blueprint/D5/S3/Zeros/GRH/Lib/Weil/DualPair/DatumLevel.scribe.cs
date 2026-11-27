using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.DualPair;

internal sealed class DatumLevelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Datum Level", H("Datum Level"),
        Blocks(
            Paragraph(Text("Finite vectors of the Weil representation are fixed by open subgroups.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/DualPair/DatumLevel.exists_level_pairWeil"),
                H("exists_level_pairWeil"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Every f in the finite part of the data space of Hom(S,T) is fixed, under the representation pairWeil with characters a, b, by K × K' for some open subgroups K, K' of the two finite adelic unitary groups.")))))));
}
