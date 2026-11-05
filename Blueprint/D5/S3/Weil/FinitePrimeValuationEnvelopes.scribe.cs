using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil;

internal sealed class FinitePrimeValuationEnvelopesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/FinitePrimeValuationEnvelopes.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint finite-prime Robin upper envelope under bounded valuations.",
        H("Finite Prime Valuation Envelopes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("joint-upper-envelope"),
                DeclarationHandle.Create(Prefix + "bounded_finite_prime_valuation_robin_ratio"),
                H("Joint finite-prime upper envelope"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every finite prime set S, prime hypotheses, exponent bound "
                    + "function A, and positive epsilon, one common threshold N at "
                    + "least 5041 bounds the actual Robin ratio by the product of "
                    + "retained Euler factors plus epsilon for every n at least N "
                    + "whose selected valuations are bounded. The proof multiplies "
                    + "the public prime-layer gain over S, takes the common layer "
                    + "count before the threshold, and then applies the existing "
                    + "Gronwall upper envelope. The exact-fibre lower construction in "
                    + "ExactPrimeValuationLowerEnvelope matches this endpoint for each "
                    + "fixed set and exponent function. For the 5040 profile "
                    + "S={2,3,5,7} with A=(4,2,1,1), the exact retained product is "
                    + "(31/32)(26/27)(24/25)(48/49)=3224/3675"))),
                DescribeRole.Theorem))));
}
