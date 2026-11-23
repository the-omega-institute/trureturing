using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class LowOrderCollisionAgreementDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/LowOrderCollisionAgreement";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two spectra agree at every degree below a prescribed threshold and differ at growing degree.",
        H("Agreement of Low-Degree Collision Masses"),
        Blocks(
            Paragraph(Text(
                "For a natural number k≥2, take the triples (0,1,k) and (0,1,k+√2) with weights "
                + "(1/4,1/4,1/2). Let E(p,t) and F(p,t) be their respective weighted ordered-pair "
                + "collision masses for degree p and closed gap bound t. In the display, the first "
                + "line holds at every natural degree p<k, and the first two lines hold for every "
                + "real t with 0≤t<1. The last two inequalities hold for every natural p>0 with "
                + "t_p=1/(2(k+3)p).")),
            Describe.Lean(
                DescribeId.Create("low-order-agreement"),
                DeclarationHandle.Create(Owner + ".low_order_agreement_and_high_order_disparity"),
                H("Coincident low-degree masses allow different high-degree rates"),
                StatementSource.FromAuthor(Masses()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Below degree k, differing counts on the last coordinate force a gap "
                        + "of at least one in both spectra. At degree k the integer spectrum gains "
                        + "the two ordered pairs between (0,k,0) and (k−1,0,1).")),
                    Paragraph(Text(
                        "At growing degree the integer spectrum keeps the mass lower bound from "
                        + "its variance. For the irrational spectrum, a nonzero integer quadratic "
                        + "norm separates all distinct degree vectors at t_p. On the remaining "
                        + "diagonal, the multinomial weights factor into two fair binomial weights. "
                        + "A central binomial bound and monotonicity in the upper tail bound their "
                        + "product. These are comparison spectra for testing what low-degree "
                        + "collision measurements determine."))),
                DescribeRole.Theorem))));

    private static Formula Masses()
    {
        var p = F.Id("p");
        var k = F.Id("k");
        var t = F.Id("t");
        var resolution = new Formula.Subscript(t, p);
        var quarter = new Formula.Fraction(D(1), D(4));
        var half = new Formula.Fraction(D(1), D(2));
        var gap = Multiply(Multiply(D(2), k),
            Multiply(new Formula.Power(Grp(quarter), Seq(k, Minus, D(1))),
                Multiply(new Formula.Power(Grp(quarter), k), half)));
        var lower = new Formula.Fraction(D(1), Multiply(Multiply(D(1, 6), k), Seq(F.Sqrt, Grp(p))));
        var upper = new Formula.Fraction(D(6), p);
        return Disp(new Formula.Aligned([
            Seq(Call("E", p, t), Sp, Eq, Sp, Call("F", p, t)),
            Seq(Call("E", k, t), Sp, Eq, Sp, Add(Call("F", k, t), gap)),
            Seq(lower, Sp, Leq, Sp, Call("E", p, resolution)),
            Seq(Call("F", p, resolution), Sp, Leq, Sp, upper)]));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
