using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class ShortCommonCoefficientProbeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive bounded integers simultaneously realize both modular Zeckendorf coefficients.",
        H("Bounded Common Zeckendorf Coefficients"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("short-common-first-index"),
                DeclarationHandle.Create(Prefix + "firstIndex"),
                H("The first Fibonacci number above twice the modulus"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a natural modulus H, firstIndex(H) is the least natural j such that "
                    + "F(j)>2H. The Fibonacci convention is F(0)=0, F(1)=1. The defining "
                    + "set is nonempty because F(k) is at least k for every k at least five."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("short-common-bounded-coefficient-pair"),
                DeclarationHandle.Create(Prefix + "bounded_coefficient_pair"),
                H("One positive integer realizes an arbitrary coefficient pair"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural H at least two, let j=firstIndex(H) and q=F(j). "
                        + "Then j is at least five and 2H<q<4H. For every A and B in ZMod H, "
                        + "there exists a natural n such that H<=n<H(q+1), n modulo H equals B, "
                        + "and shiftedFibSum(n) modulo H equals A. Here shiftedFibSum(n) is "
                        + "the sum of F(k-1) over the canonical Zeckendorf indices k of n. "
                        + "The same n realizes both coordinates, including the pair (0,0).")),
                    Paragraph(Text(
                        "Write alpha for the inverse golden ratio. Consecutive Fibonacci "
                        + "numbers p=F(j-1) and q are coprime, and the approximation "
                        + "|alpha-p/q|<1/(2q^2) controls a complete shifted rational grid. "
                        + "Choose representatives a and b between zero and H-1. Rounding "
                        + "the target cell midpoint and using a Bezout identity selects one "
                        + "integer t with 1<=t<=q. Its perturbed grid point lies strictly "
                        + "inside the cell (a/H,(a+1)/H). Thus n=b+Ht has the required "
                        + "bound and floor((n+1)alpha) is congruent to a. The shifted "
                        + "Zeckendorf floor identity supplies the second coefficient."))),
                DescribeRole.Theorem))));
}
