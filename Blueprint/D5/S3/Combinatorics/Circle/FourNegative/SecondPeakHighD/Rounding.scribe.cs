using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD;
internal sealed class RoundingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed ceiling and parity remainder", H("Signed ceiling and parity remainder"),
        Blocks(
            Paragraph(Text("The signed integer ceiling works for negative numerators as well as positive ones. Choosing M=D*ceil((K-B+L)/(D*L))-1 places the second remainder in [0,D*L), and a dyadic D makes all low bits available. Parity adjustment chooses j in the required congruence class and proves the exact first remainder before converting integers to natural masks."))), []));
}
