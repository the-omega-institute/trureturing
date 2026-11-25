using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio;

internal sealed class QuarticPrimeWitnessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FactorialRatio/QuarticPrimeWitness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A selected family member for each prime",
        H("Quartic compact factorial gcd"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("quartic-prime-witness"),
                DeclarationHandle.Create(Prefix + "quartic_prime_witness"),
                H("A selected family member for each prime"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At s=(r-1)(r-2), the zero parameter bounds the small-prime exponent excess "
                    + "by 3(r-1) times the integer base-p logarithm of r. For r<p<=s, "
                    + "Dirichlet approximation or the parameter floor(p/r) gives an admissible member. "
                    + "The paired floors telescope to a residue count. Folding the last quotient bin "
                    + "into the first bounds that count by a sum of integer interval lengths. "
                    + "Only the first prime power contributes, with excess at most 4r/sqrt(p). "
                    + "For p>s the zero parameter gives exponent zero."))),
                DescribeRole.Theorem))));
}
