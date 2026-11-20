using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using Dsl = StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.CellularAutomata;

internal sealed class HoneycombBirthKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adjacent-cut birth polynomials and their normalized honeycomb kernels.",
        H("Birth polynomials of adjacent honeycomb cuts"),
        Blocks(
            Paragraph(Text("For height a and cut d, retain nonnegative coordinates with "
                + "x+y<a and g<2a−d. Sum one monomial per birth, whose exponent is its "
                + "tick. The signed polynomial Δ(a,d) subtracts the result for cut d+1 "
                + "from the result for cut d. Its coefficient at tick t sums the "
                + "zero-extended differences of the two birth indicators.")),
            Paragraph(Text("At a positive multiple a of a dyadic strip width P, horizontal "
                + "translation identifies the right strip with the height-P run after "
                + "a delay of 2(a−P). The exterior-left birth indicators agree between "
                + "the cuts there. Thus for c+1 ≤ P the adjacent-cut difference satisfies "),
                Math(DyadicCopy()), Text(".")),
            Paragraph(Text("At neighboring cuts of an integral height, let τ=2a−d−1. "
                + "The potential 2τ−g+y changes by at most one along an edge before "
                + "nonnegative truncation. On the removed layer it equals the earliest "
                + "possible touch time. This gives zero coefficients below τ and places "
                + "any nonzero signed weight at time τ+j on a layer g=τ−i with i+y≤j.")),
            Paragraph(Text("Removing the delay gives the integer polynomial in equation (17). "
                + "The kernel uses the least dyadic a above d, and the strip identity "
                + "makes the coefficient independent of the choice of eligible dyadic "
                + "enclosure.")))));

    private static Formula DyadicCopy()
    {
        var a = Dsl.Id("a");
        var c = Dsl.Id("c");
        var p = Dsl.Id("P");
        var delay = Multiply(Num(2), Parenthesized(Subtract(a, p)));
        return Equal(new Formula.Apply(Delta, [a, c]),
            Multiply(new Formula.Power(Dsl.Id("z"), delay),
                new Formula.Apply(Delta, [p, c])));
    }

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
