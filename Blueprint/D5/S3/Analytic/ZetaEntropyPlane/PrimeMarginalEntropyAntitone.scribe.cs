using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaEntropyPlane;

internal sealed class PrimeMarginalEntropyAntitoneDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/ZetaEntropyPlane/PrimeMarginalEntropyAntitone.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Larger primes carry strictly less complete exponent entropy at fixed temperature.",
        H("Prime Marginal Entropy Antitonicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("geometric-entropy-ratio-function"),
                DeclarationHandle.Create(Prefix + "hGeom"),
                H("Geometric entropy as a ratio function"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The named function hGeom is minus log of one minus the ratio, minus "
                        + "the ratio odds multiplied by the log ratio. Naming it exposes the "
                        + "definition independently of the later monotonicity theorem."))),
                DescribeRole.Definition
            ),
            Describe.Lean(
                DescribeId.Create("geometric-entropy-totalized-endpoint-values"),
                DeclarationHandle.Create(Prefix + "hGeom_endpoint_values"),
                H("The totalized endpoint values are both zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Lean's real logarithm and division are totalized. Direct substitution "
                        + "therefore gives hGeom value zero at both ratio zero and ratio one, "
                        + "even though the left limit at one is unbounded."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("geometric-entropy-strictly-increases"),
                DeclarationHandle.Create(Prefix + "hGeom_strictMonoOn"),
                H("Geometric entropy strictly increases inside the unit interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On ratios strictly between zero and one, differentiation gives minus "
                        + "log of the ratio divided by the square of one minus the ratio. "
                        + "The logarithm is negative there, so the derivative is positive."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("geometric-entropy-includes-lower-endpoint"),
                DeclarationHandle.Create(Prefix + "hGeom_strictMonoOn_Ico"),
                H("The lower endpoint may be included"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Strict increase extends to the half-open interval containing zero. The "
                        + "endpoint value is zero, while every interior geometric entropy is "
                        + "strictly positive."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("upper-endpoint-must-remain-excluded"),
                DeclarationHandle.Create(Prefix + "upper_endpoint_is_necessary"),
                H("The upper endpoint must remain excluded"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Including ratio one contradicts strict increase under totalization: the "
                        + "interior ratio one half has positive entropy, whereas hGeom at one "
                        + "is zero. This is a concrete named endpoint counterexample."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-exponent-reverses-prime-order"),
                DeclarationHandle.Create(Prefix + "prime_rpow_lt_of_lt"),
                H("A positive negative-power exponent reverses prime order"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any positive real exponent, a strict increase in prime value gives a "
                        + "strict decrease in its negative real power. This step needs only "
                        + "positivity of the exponent, not the stronger convergence bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-exponent-is-necessary"),
                DeclarationHandle.Create(Prefix + "positive_exponent_is_necessary"),
                H("Exponent positivity is necessary"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At exponent zero, the ordered primes two and three both have weight one. "
                        + "Their strict negative-power comparison therefore fails, furnishing "
                        + "the required concrete counterexample."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-three-weight-order-at-one"),
                DeclarationHandle.Create(Prefix + "two_three_rpow_at_one"),
                H("The two-three weight order remains strict at exponent one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For the smallest ordered prime pair, three to the power minus one is "
                        + "strictly smaller than two to the power minus one. Thus the power "
                        + "comparison itself does not require inverse temperature above one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-entropy-is-geometric-entropy"),
                DeclarationHandle.Create(Prefix + "primeExponent_entropy_eq_hGeom"),
                H("Prime-exponent entropy is hGeom at the prime ratio"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The existing closed form for the complete prime-exponent marginal is "
                        + "rewritten exactly as hGeom evaluated at the prime to the power minus "
                        + "the inverse temperature. No entropy sum is reproved here."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-entropy-strictly-antitone"),
                DeclarationHandle.Create(Prefix + "primeExponent_entropy_strictAntitone"),
                H("Complete exponent entropy strictly decreases with the prime"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Above inverse temperature one, ordered primes give oppositely ordered "
                        + "ratios inside the open unit interval. Strict increase of hGeom then "
                        + "makes the larger prime's complete exponent entropy smaller."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("strict-prime-order-is-necessary"),
                DeclarationHandle.Create(Prefix + "strict_prime_order_is_necessary"),
                H("Strict prime order is necessary"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Using prime two on both sides makes both the negative-power comparison "
                        + "and the corresponding entropy comparison irreflexive. This concrete "
                        + "case records why a strict prime-value hypothesis is required."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-three-entropy-order"),
                DeclarationHandle.Create(Prefix + "two_three_entropy_strict"),
                H("Prime three has less exponent entropy than prime two"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every admissible inverse temperature, the complete exponent marginal "
                        + "at prime three has strictly smaller countable entropy than the one at "
                        + "prime two. This instantiates the result at the smallest prime pair."))),
                DescribeRole.Theorem))));
}
