using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ExponentExchange;

internal sealed class AbundancyRecord5040Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ExponentExchange/AbundancyRecord5040.";
    private static readonly LibraryNoteRef AE = LibraryNoteRef.Create("D5/L/Arith/alaoglu1944highly");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual one-layer prime exchange forces 5040 to divide large strict abundancy records.",
        H("Actual Prime-Layer Exchange and Abundancy Records"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-one-layer-abundancy-exchange"),
                DeclarationHandle.Create(Prefix + "one_layer_abundancy_exchange"),
                H("A smaller actual integer with larger abundancy"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(AE),
                Blocks(
                    Paragraph(Text(
                        "Let m be a positive natural number, p and q primes, and k>=1. "
                        + "Assume q divides m, the sum B(p,k)=p+...+p^k is below q, and "
                        + "the p-exponent of m is below k. The actual integer m'=(m/q)*p "
                        + "is positive and strictly smaller than m, and sigma(1,m')/m' "
                        + "is strictly larger than sigma(1,m)/m.")),
                    Paragraph(Text(
                        "At price zero the exact single-layer resource identity gives "
                        + "W(m')-W(m)=log(1+1/B(p,a+1))-log(1+1/B(q,b)), where "
                        + "a=v_p(m) and b=v_q(m)>=1. The first denominator is at most "
                        + "B(p,k)<q<=B(q,b). Strict monotonicity of the reciprocal and "
                        + "logarithm proves the gain. This removes one copy of q and "
                        + "inserts one copy of p; no full-exponent exchange is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("strict-abundancy-record-literal-5040"),
                DeclarationHandle.Create(Prefix + "strict_abundancy_record_divisible_5040"),
                H("The literal 5040 core"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(AE),
                Blocks(
                    Paragraph(Text(
                        "For every positive natural m, assume sigma(1,m)/m>30 and a strict "
                        + "abundancy record against every positive natural n<m, including one "
                        + "and two. Then the literal integer 5040 divides m.")),
                    Paragraph(Text(
                        "The exact Euler factors bound sigma(1,m)/m by the product of "
                        + "p/(p-1) over its prime support. If all primes were at most thirty, "
                        + "padding to every integer from two through thirty would give the "
                        + "telescoping upper bound thirty. Hence an actual prime q>30 "
                        + "divides m. A missing layer among (2,4),(3,2),(5,1),(7,1) would "
                        + "have denominator at most thirty and permit the preceding smaller "
                        + "integer exchange, contradicting the record. The pairwise coprime "
                        + "powers 16,9,5,7 therefore divide m and have product 5040.")),
                    Paragraph(Text(
                        "This is an application of the classical superabundant-number "
                        + "exchange method, with no claim of literature priority. It does "
                        + "not assert that such records occur at any particular scale, "
                        + "nor prove a Robin upper inequality or RH."))),
                DescribeRole.Theorem))));
}
