using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers;
internal sealed class PeakMasksDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Physical peak masks",
        H("First reserve and binary support"),
        Blocks(Paragraph(Text("For a strict middle peak, the first reserve uses a high U bit and a low mask two or three when T is at least four times Z. At the adjacent ratio T=2Z, it advances the V mask n and retains the U mask 8n+3, where n is the nonnegative ceiling of (e1-3A)/(8A-2e1). The effective reserve lies between e1 and 2e1-A. Both masks fit their physical chains, and the retained low mask is a subset of the actual U mask. The two branches include the smallest allowed gaps and equal outer gaps."))), []));
}
