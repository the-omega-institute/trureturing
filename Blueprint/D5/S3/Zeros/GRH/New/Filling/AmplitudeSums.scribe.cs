using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Filling;

internal sealed class AmplitudeSumsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Amplitude Sums", H("Amplitude Sums"),
        Blocks(
            Paragraph(Text("Blocks of the unfolded moment: convergence, cut, weight change, moves, identity term.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Filling/AmplitudeSums.amplitudeSum_besselS_one"),
                H("amplitudeSum_besselS_one"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let T be the group of rational points of the Bessel subgroup 𝖴H. The sum of the amplitudes of the elements of T over (c, 1, c') has (i, j) entry ν = Filling.unipCovolume if c = c' and i = j, and 0 otherwise.")))))));
}
