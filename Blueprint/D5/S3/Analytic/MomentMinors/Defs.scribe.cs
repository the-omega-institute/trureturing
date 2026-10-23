using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.MomentMinors;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Moment gaps and their second minors.",
        H("Probability laws and parameter intervals"), Blocks(
            Paragraph(Text("A law is a Borel probability measure on the real line concentrated on strictly positive values. Its first moment is integrable. Every real power indexed by the interval is integrable, and the logarithmic moment and the first logarithmic moment are integrable when the interval contains zero and one, respectively.")),
            Paragraph(Text("The normalized moment gap is the difference between the power moment and the power of the mean, divided by s(s-1). At zero it is the logarithm of the mean minus the logarithmic moment. At one it is the first logarithmic moment minus the mean times its logarithm.")),
            Paragraph(Text("The function xi is the second principal minor of the midpoint moment kernel. The function phi is a second minor formed from xi and the alternating cross entries. Restricting xi to pairs with common displacement a gives sigma; its midpoint minor is theta.")),
            Paragraph(Text("The first claim asserts the eight-parameter inequality between products of phi and the square of the alternating cross expression. The second claim asserts the corresponding inequality for theta. All endpoint parameters belong to one interval, which also contains every midpoint occurring in the formulas. The combined claim is their conjunction.")))));
}
