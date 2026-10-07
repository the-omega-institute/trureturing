using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Covering;

internal sealed class TwoPrimeSupportObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Covering/TwoPrimeSupportObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A whole distinct odd cover cannot have a common modulus supported on only two odd primes.",
        H("Two-Prime Support Obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("two-prime-supported-common-modulus-impossible"),
                DeclarationHandle.Create(Prefix + "no_two_odd_prime_supported_common_modulus"),
                H("Two-prime-supported common moduli are impossible"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let S be a distinct odd covering system whose common modulus is "
                            + "p^A * q^B for distinct odd primes p and q. Map each original "
                            + "modulus to its finite residue class and use injectivity to retain "
                            + "the corresponding residue label.")),
                    Paragraph(Text(
                        "The existing two-odd-prime uncovered-density theorem then supplies an "
                            + "uncovered residue, contradicting the whole-cover property. This "
                            + "only excludes the two-prime-support branch."))),
                DescribeRole.Theorem))));
}
