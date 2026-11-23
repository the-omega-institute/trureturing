using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class PrimeProductCollisionBudgetsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/PrimeProductCollisionBudgets";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common integer shift controls the excess collision mass across prime products.",
        H("Prime Products and Weighted Collision Excess"),
        Blocks(
            Paragraph(Text(
                "Take a finite indexed integer spectrum with nonnegative real weights of sum W. "
                + "Fix natural numbers p, H, D, r, B and Q, with Q at least 2. Give each ordered pair "
                + "of degree-p count vectors the product of its two weighted multinomial coefficients. "
                + "Assume that every such pair has absolute integer gap at most D. Let L be the "
                + "weighted mass of pairs with absolute gap at most H. For a modulus q let C(q) "
                + "denote the mass of pairs whose gap modulo q is the image of an integer in [−H,H]. "
                + "Let P be a finite set of primes at least Q. Assume that D+H is strictly less than "
                + "Q to the power B+1.")),
            Paragraph(Text(
                "Write E for the sum of C(q) minus L over all r-element subsets of P, using the "
                + "product of the primes in each subset as q. Write choose(n,r) for the binomial "
                + "coefficient, including the value zero when r exceeds n.")),
            Describe.Lean(
                DescribeId.Create("sum-prime-product-cyclic-excess"),
                DeclarationHandle.Create(Owner + ".sum_prime_product_cyclic_excess_le"),
                H("An upper bound on the sum of product-modulus excesses"),
                StatementSource.FromAuthor(Excess()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an off-band gap d, each product modulus that counts the pair gives one "
                    + "shift y in the band. Every prime in that subset divides the same nonzero "
                    + "integer d−y. The single-prime counting bound at radius zero gives at most B "
                    + "eligible primes for each shift. Take the union of the families of r-element "
                    + "subsets over all 2H+1 shifts and sum the resulting incidence bound against "
                    + "the off-band pair weights."))),
                DescribeRole.Theorem))));

    private static Formula Excess()
    {
        var r = F.Id("r");
        var L = F.Id("L");
        var E = F.Id("E");
        var size = new Formula.Absolute(F.Id("P"));
        var shifts = Seq(Open, Multiply(D(2), F.Id("H")), Plus, D(1), Close);
        var cap = Call("min", Call("choose", size, r),
            Multiply(shifts, Call("choose", Call("min", F.Id("B"), size), r)));
        var total = new Formula.Power(F.Id("W"), Multiply(D(2), F.Id("p")));
        return Disp(Seq(D(0), Sp, Leq, Sp, E, Sp, Leq, Sp,
            Multiply(cap, Seq(Open, total, Minus, L, Close))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
