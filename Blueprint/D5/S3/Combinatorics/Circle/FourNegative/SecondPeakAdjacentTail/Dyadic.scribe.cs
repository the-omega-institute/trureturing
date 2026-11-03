using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail;
internal sealed class DyadicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dyadic residues and exact integer quotients", H("Paired source arithmetic"),
        Blocks(
            Paragraph(Text("Euclidean division c+s=a ell+j gives 0<=j<a and 2^(c+s) congruent to (-1)^ell 2^j modulo 2^a+1. The representative is 2^j for even ell and 2^a+1-2^j for odd ell, with an exact integer quotient.")),
            Paragraph(Text("Exponents in the same class modulo 2a have powers differing by a nonnegative multiple of 2^a+1. The q=4 lower orthants follow from the exponent identity and parity of ell, so they hold for every unbounded natural c."))), []));
}
