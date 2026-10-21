using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.InterlaceFan;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Interlace functionals and rational faces of their fan.",
        H("Interlace fan definitions"), Blocks(
            Paragraph(Text("For darga n, a real coordinate vector has entries indexed from one through floor(n/2). Its j-th interlace functional is minus the sum of the coordinates multiplied by cos(2 pi j k/n). Certificate indices run from zero through floor(n/2), and the interlace number is the largest functional value.")),
            Paragraph(Text("The closed face associated with S consists of all vectors for which every index in S attains this maximum. Rational points have rational coordinates. The order class for a divisor d consists of the indices j with n/gcd(n,j)=d.")),
            Paragraph(Text("The classification proposition states that a nonempty certificate set admits a nonzero rational point precisely when it misses an order class; the maximal such certificate sets are the complements of individual order classes. At a nonzero rational point of the corresponding face, all excluded indices have strictly smaller functional value and the interlace number is rational. These definitions use the sigma-coordinate convention of equation (12) in Mandel and Robins, Dragging the roots of a polynomial to the unit circle, arXiv:1908.03208, section 5.2 and Problem 3.")))));
}
