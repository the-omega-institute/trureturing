using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Covering;

internal sealed class PrimeSupportInitialSegmentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Covering/PrimeSupportInitialSegment.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Minimal odd distinct covers have an initial segment of odd prime support.",
        H("Prime-Support Initial Segment"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("odd-prime-product-dvd-common-modulus"),
                DeclarationHandle.Create(Prefix + "odd_prime_product_dvd_commonModulus"),
                H("The common modulus contains the smaller odd-prime product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let F be a distinct odd covering system that is minimal first "
                            + "in its number of classes and then in the sum of its moduli. "
                            + "If a prime q divides the common modulus, then the product "
                            + "of every odd prime below q also divides that common modulus.")),
                    Paragraph(Text(
                        "The proof applies the prime-support gap descent to each smaller "
                            + "odd prime and then combines the resulting pairwise-coprime "
                            + "divisibilities by finite induction. This records a support "
                            + "prefix for a minimal counterexample; it does not prove that "
                            + "an unrestricted odd covering system cannot exist."))),
                DescribeRole.Theorem))));
}
