using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class PrimeCyclicCollisionBudgetsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/PrimeCyclicCollisionBudgets";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A product of shifted gaps bounds the weighted excess caused by modular wraparound.",
        H("Prime Moduli and Weighted Collision Excess"),
        Blocks(
            Paragraph(Text(
                "Take a finite indexed integer spectrum with nonnegative real weights w. "
                + "Let p, H, D, Q and B be natural numbers. Each ordered pair of degree-p count "
                + "vectors has weight equal to the product of its two weighted multinomial "
                + "coefficients. Let L be the mass of pairs with absolute integer gap at most H, "
                + "and C(q) the mass obtained by testing the gap modulo q against the image "
                + "of the closed integer band [−H,H]. Write W for the sum of the base weights. "
                + "Let P be a finite set of primes at least Q, with Q≥2. "
                + "Suppose every degree-p gap has absolute value at most D. "
                + "Assume that Q to the power B+1 strictly exceeds the product "
                + "of |D−y| over the integers y in [−H,H].")),
            Describe.Lean(
                DescribeId.Create("band-alias-card"),
                DeclarationHandle.Create(Owner + ".band_alias_card_le"),
                H("A count of prime moduli for a single off-band gap"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("n"), Sp, Leq, Sp, F.Id("B")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For one integer gap d with H < |d| ≤ D, n counts the primes in P "
                    + "for which the residue of d is the image of some band shift. Each such "
                    + "prime divides the nonzero product of the absolute shifted gaps."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sum-cyclic-excess"),
                DeclarationHandle.Create(Owner + ".sum_cyclic_excess_le"),
                H("An upper bound on the sum of modular excesses"),
                StatementSource.FromAuthor(Excess()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an off-band pair, every prime modulus that counts it divides the nonzero "
                    + "product of the shifted gaps. The product of all such primes divides that "
                    + "integer. Comparing with powers of Q bounds the number of moduli that count "
                    + "the pair. Changing the order of summation gives the weighted bound."))),
                DescribeRole.Theorem))));

    private static Formula Excess()
    {
        var q = F.Id("q");
        var p = F.Id("p");
        var W = F.Id("W");
        var L = F.Id("L");
        var primeSet = F.Id("P");
        var excess = Seq(new Formula.Subscript(Sum, Seq(q, Sp, InMacro, Sp, primeSet)),
            Sp, Seq(Open, Call("C", q), Minus, L, Close));
        var cap = Multiply(Call("min", F.Id("B"), new Formula.Absolute(primeSet)),
            Seq(Open, new Formula.Power(W, Multiply(D(2), p)), Minus, L, Close));
        return Disp(Seq(D(0), Sp, Leq, Sp, excess, Sp, Leq, Sp, cap));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
