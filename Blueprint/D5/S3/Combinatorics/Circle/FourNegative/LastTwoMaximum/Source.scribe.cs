using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum;
internal sealed class SourceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact tied-maximum source dictionary", H("Original heads and selectors"),
        Blocks(Paragraph(Text("The private dictionary preserves gaps (a,b,s,s) and seed 1+2^a+2^(a+b)+2^(a+b+s). It defines the old and new heads, both residuals, the natural quotient, hybrid dyadic masses, and exact borrow and singleton selectors. The hybrid decomposition is consumed by both physical source proofs. Actual source identities, the eight recurrences, source signs and zero totals are reused through canonical PacketNormalForm and native_masses rather than carried as unused local reproofs. The pre-fresh new total is -A; the actual fresh A gives the new zero total."))), []));
}
