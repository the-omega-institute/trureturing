using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio;

internal sealed class BalaA295462QuotientDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The A295462 factorial quotient divided by (6n+1)(10n+1) is a positive integer, "
            + "odd exactly when the binary positions of n are four-separated.",
        H("The reduced A295462 quotient"),
        Blocks(Describe.Lean(
            DescribeId.Create("bala-a295462-reduced-quotient"),
            DeclarationHandle.Create(
                "D5/S3/Arith/FactorialRatio/BalaA295462Quotient.reduced_quotient"),
            H("Integrality, positivity and parity of the reduced quotient"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let a(n)=(15n)!(2n)!/((10n)!(6n)!n!) as a rational number. For every "
                    + "natural n there is a natural number b with 0<b, "
                    + "a(n)/((6n+1)(10n+1))=b, and b odd if and only if any two distinct "
                    + "occupied binary positions of n differ by at least four.")),
                Paragraph(Text(
                    "The quotient a(n) is a natural number m with the same parity criterion. "
                    + "For every modulus q≥2, the floor inequality "
                    + "⌊10n/q⌋+⌊(6n+1)/q⌋+⌊n/q⌋≤⌊15n/q⌋+⌊2n/q⌋ holds; summing it over the "
                    + "prime powers q=p^j gives (10n)!(6n+1)!n!∣(15n)!(2n)!, so 6n+1 divides m. "
                    + "Writing n=Qq+r with r<q reduces the inequality to r. When q does not "
                    + "divide 6r+1 it is the ordinary nonnegativity of "
                    + "⌊15x⌋+⌊2x⌋−⌊10x⌋−⌊6x⌋−⌊x⌋ on the grid of multiples of 1/30. When "
                    + "6r+1=tq, parity and residues modulo three leave t∈{1,5}, and "
                    + "⌊30r/q⌋=5t−1 settles both cases. With ⌊(10n+1)/q⌋ in place of "
                    + "⌊10n/q⌋ the reduction is the same; when 10r+1=tq, parity and "
                    + "residues modulo five leave t∈{1,3,7,9}, and ⌊30r/q⌋=3t−1 settles "
                    + "each case, so 10n+1 divides m.")),
                Paragraph(Text(
                    "Since 5(6n+1)−3(10n+1)=2 and both factors are odd, they are coprime, so "
                    + "their product divides m. The product is odd, so b=m/((6n+1)(10n+1)) "
                    + "has the parity of m, and it is positive because m is."))),
            DescribeRole.Theorem))));
}
