using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class CyclicGrowingRearSecondOrderDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Asymptotics/CyclicGrowingRearSecondOrder";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A quadratic correction resolves the zero first-order rear activation margin.",
        H("Second-order rear activation"),
        Blocks(
            Paragraph(Text(
                "Fix a nonempty finite rear offset set S and mesh sequence h. Define Q_n=3n⁵h(n)²/20. " +
                "Assume Q_n→Q=3K/20, n(Q_n−Q)→L and n(n(Q_n−Q)−L)→H. " +
                "For an offset r, set D=|S|r²−∑_{s∈S}s² and denote the signed rear weight by p_n(r).")),
            Describe.Lean(DescribeId.Create("rear-second-order"),
                DeclarationHandle.Create(Owner + ".scaled_rear_second_order"),
                H("Second-order signed rear value"),
                StatementSource.FromAuthor(SecondOrder()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The exact normalizer yields n(n(C_lat+3/4)−9/8)→−15/8, and the cubic " +
                    "coefficient-error bound transfers this to C_n. The uniform front contribution " +
                    "and finite rear feature errors vanish after quadratic amplification. Therefore " +
                    "the amplified bottom-row and point-readout errors also vanish at that scale. " +
                    "Eliminate B_n using the exact target Q_n(1+1/n) to obtain the second-order limit."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("second-order-threshold-support"),
                DeclarationHandle.Create(Owner + ".eventual_support_at_second_order_threshold"),
                H("Support when the first-order margin vanishes"),
                StatementSource.FromAuthor(Selection()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Suppose q(n)>0 are integer periods of eventual parity e, h(n)=2π/q(n), " +
                        "Q=T_e(l+1), and L+5Q/2=0. The disputed outer level has 3D/4=Q for " +
                        "both adjacent windows. The quadratic correction is H−5Q. If this is " +
                        "nonzero, the selected index k is l+1 for positive correction and l for negative correction.")),
                    Paragraph(Text(
                        "The other endpoint signs are strict at the leading scale. The finite certificate " +
                        "gives feasibility, both exact cosine moment floors, uniqueness and the squared-distance " +
                        "energy inequality. The positive support consists of the front window and the selected " +
                        "rear window. The further degeneracy H=5Q is excluded."))),
                DescribeRole.Theorem))));

    private static Formula SecondOrder()
    {
        var n = F.Id("n");
        var d = F.Id("D");
        var q = F.Id("Q");
        var l = F.Id("L");
        var r = F.Id("r");
        var p = Mul(Mul(Call("Card", F.Id("S")),
            new Formula.Power(n, F.D(3))), Call("RearValue", n, r));
        var first = Sub(Mul(n, Sub(p, Sub(q, Mul(Frac(3, 4), d)))),
            Add(Add(l, q), Mul(Frac(9, 8), d)));
        var right = Sub(Add(F.Id("H"), l), Mul(Frac(15, 8), d));
        return F.Disp(Eq(Call("Limit", Mul(n, first)), right));
    }

    private static Formula Selection()
    {
        var margin = Sub(F.Id("H"), Mul(F.D(5), F.Id("Q")));
        var l = F.Id("l");
        var k = F.Id("k");
        var positive = new Formula.Logic(
            new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, margin),
            FormulaLogicOperator.Implies, Eq(k, Add(l, F.D(1))));
        var negative = new Formula.Logic(
            new Formula.Relation(margin, FormulaRelationOperator.LessThan, F.D(0)),
            FormulaLogicOperator.Implies, Eq(k, l));
        return F.Disp(new Formula.Logic(positive, FormulaLogicOperator.And, negative));
    }

    private static Formula Frac(byte a, byte b) =>
        new Formula.Fraction(a <= 9 ? F.D(a) : F.Seq(F.D((byte)(a / 10)), F.D((byte)(a % 10))), F.D(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
}
