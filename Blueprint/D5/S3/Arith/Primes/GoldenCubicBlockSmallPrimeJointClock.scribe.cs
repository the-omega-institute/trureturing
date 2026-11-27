using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class GoldenCubicBlockSmallPrimeJointClockDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two small-prime readouts of one Lucas block compose differently with odd witness clocks.",
        H("Synchronizing the small-prime Lucas readouts"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-cubic-dyadic-witness-pair"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicBlockSmallPrimeJointClock.dyadic_witness_pair_exists"),
                H("Exact compatibility of dyadic and odd witness readings"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The time labels have to agree modulo the greatest common divisor "
                    + "of their periods. For witnesses congruent to three modulo four, "
                    + "the odd witness period is odd and no constraint remains."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-dyadic-native-parity-obstruction"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicBlockSmallPrimeJointClock.native_dyadic_parity_obstruction"),
                H("A witnessed failure of dyadic independence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The prime 1277209 occurs at level six to depth one and has an even "
                    + "base-nine clock. At precision 256 and 1277209 cubed, opposite time "
                    + "parities give two separately attainable but incompatible readings."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-three-witness-pair"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicBlockSmallPrimeJointClock.three_witness_pair_exists"),
                H("A transient at three fixes the time, but the fixed residue does not"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A genuinely transient reading modulo a power of three can occur at only "
                    + "one time. Once its fixed residue is reached, every available periodic "
                    + "witness phase can be represented at a sufficiently late index."))),
                DescribeRole.Theorem))));
}
