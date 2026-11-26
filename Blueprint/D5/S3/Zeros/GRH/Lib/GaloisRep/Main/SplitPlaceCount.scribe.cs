using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GaloisRep.Main;

internal sealed class SplitPlaceCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Split Place Count", H("Split Place Count"),
        Blocks(
            Paragraph(Text("Enough places above a split quadratic place, using roots of unity.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GaloisRep/Main/SplitPlaceCount.exists_place_above_ne"),
                H("exists_place_above_ne"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For E stably unramified containing K = ℚ(√−d), u a split place of K prime to d (IsSplitPrimeToDisc) and any places a, b of E, some place of E above u differs from a and b.")))))));
}
