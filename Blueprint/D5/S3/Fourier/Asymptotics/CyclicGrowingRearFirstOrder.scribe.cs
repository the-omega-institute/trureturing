using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class CyclicGrowingRearFirstOrderDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Asymptotics/CyclicGrowingRearFirstOrder";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A first-order expansion selects the adjacent rear support even at a leading activation threshold.",
        H("First-order rear activation"),
        Blocks(
            Paragraph(Text(
                "Fix a nonempty finite rear offset set S and mesh sequence h. Write Q_n=3n⁵h(n)²/20, " +
                "suppose n⁵h(n)²→K, Q=3K/20, and n(Q_n−Q)→L. For a real offset r, define " +
                "D=|S|r²−∑_{s∈S}s². The signed rear value p_n(r) uses the coupled three-moment fit.")),
            Describe.Lean(DescribeId.Create("quadratic-remainders"),
                DeclarationHandle.Create(Owner + ".second_order_remainders"),
                H("Quadratically amplified moment and point errors"),
                StatementSource.FromAuthor(Remainders()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a convergent finite critical scale n⁵h(n)², the exact bottom moment " +
                    "target minus C_n∑_{s∈S}s²+|S|B_n vanishes after multiplication by n². " +
                    "At any fixed real offset r the error n³p_n(r)−(C_n r²+B_n) also vanishes " +
                    "after multiplication by n². Uniform front bounds and the quadratic " +
                    "trigonometric remainder on each fixed rear offset give both limits."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rear-first-order"),
                DeclarationHandle.Create(Owner + ".scaled_rear_first_order"),
                H("First-order signed rear value"),
                StatementSource.FromAuthor(FirstOrder()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The exact lattice normalizer is (4/3)n³+2n²−n/3−1/2. The refined front-coefficient " +
                    "estimate transfers n(C_n+3/4)→9/8 to the coupled fit. The bottom moment row differs " +
                    "from (0,∑_{s∈S}s²,|S|) by o(1/n). Uniform bounds on the growing front and pointwise " +
                    "bounds on the finite rear set prove this rate. The point readout differs from " +
                    "C_n r²+B_n by o(1/n) after scaling by n³. Eliminating B_n using the exact bottom " +
                    "target Q_n(1+1/n) gives the displayed limit."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("threshold-support"),
                DeclarationHandle.Create(Owner + ".eventual_support_at_threshold"),
                H("Support at leading threshold equality"),
                StatementSource.FromAuthor(Margin()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let q(n)>0 be integral, h(n)=2π/q(n), and let e be the eventual parity. Fix " +
                        "l≥0 with Q=T_e(l+1). If L+5Q/2 is nonzero, the adjacent support index is l+1 " +
                        "when this quantity is positive and l otherwise.")),
                    Paragraph(Text(
                        "The two adjacent candidate windows have the same zero-boundary threshold " +
                        "identity. The first-order limit controls the sign at that level. The other " +
                        "rear boundary and both front boundaries have strict leading signs, so the " +
                        "full finite optimizer certificate applies. The fitted law is feasible, both " +
                        "cosine moments equal 1−2n(n+1)h²/5, and energy exceeds its minimum by at least " +
                        "the squared distance to the fitted law. Its exact positive support is the " +
                        "front and selected rear window. The further degeneracy L+5Q/2=0 is excluded."))),
                DescribeRole.Theorem))));

    private static Formula Remainders()
    {
        var n = F.Id("n");
        var scale = new Formula.Power(n, F.D(2));
        var moment = new Formula.Relation(Call("Limit", Mul(scale, Call("MomentError", n))),
            FormulaRelationOperator.Equal, F.D(0));
        var point = new Formula.Relation(Call("Limit", Mul(scale, Call("PointError", n, F.Id("r")))),
            FormulaRelationOperator.Equal, F.D(0));
        return F.Disp(new Formula.Logic(moment, FormulaLogicOperator.And, point));
    }

    private static Formula FirstOrder()
    {
        var n = F.Id("n");
        var d = F.Id("D");
        var q = F.Id("Q");
        var l = F.Id("L");
        var r = F.Id("r");
        var left = Mul(n, Sub(Mul(Mul(Call("Card", F.Id("S")),
            new Formula.Power(n, F.D(3))), Call("RearValue", n, r)), Sub(q, Mul(Frac(3, 4), d))));
        return F.Disp(new Formula.Relation(Call("Limit", left), FormulaRelationOperator.Equal,
            Add(Add(l, q), Mul(Frac(9, 8), d))));
    }

    private static Formula Margin()
    {
        var margin = Add(F.Id("L"), Mul(Frac(5, 2), F.Id("Q")));
        var l = F.Id("l");
        var k = F.Id("k");
        var positive = new Formula.Logic(
            new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, margin),
            FormulaLogicOperator.Implies,
            new Formula.Relation(k, FormulaRelationOperator.Equal, Add(l, F.D(1))));
        var negative = new Formula.Logic(
            new Formula.Relation(margin, FormulaRelationOperator.LessThan, F.D(0)),
            FormulaLogicOperator.Implies,
            new Formula.Relation(k, FormulaRelationOperator.Equal, l));
        return F.Disp(new Formula.Logic(positive, FormulaLogicOperator.And, negative));
    }

    private static Formula Frac(byte a, byte b) => new Formula.Fraction(F.D(a), F.D(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
}
