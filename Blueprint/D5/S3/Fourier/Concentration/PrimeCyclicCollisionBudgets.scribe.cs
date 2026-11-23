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
                "Take a finite integer spectrum with nonnegative weights w and degree p. "
                + "Let L be the weighted mass of ordered pairs whose integer gap has absolute value "
                + "at most the integer H≥0, and C(q) their cyclic band mass modulo q. "
                + "Write W for the sum of the weights. Let P be a finite set of primes at least Q≥2. "
                + "Suppose every integer gap has absolute value at most D. "
                + "For B≥0 assume that Q to the power B+1 exceeds "
                + "the product of the absolute values of D−y over integers y in [−H,H].")),
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
