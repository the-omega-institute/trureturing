using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens;

internal sealed class RobinWeightedTailConverseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Mertens/RobinWeightedTailConverse.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Negative excursions of the exact Robin weighted tail and the converse to its lower bound.",
        H("Robin Weighted Tail Converse"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("normalized-weighted-tail-negative-peaks"),
                DeclarationHandle.Create(Prefix + "normalized_weighted_tail_negative_peaks"),
                H("Negative excursions forced by a right half-strip zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let rho be a zero of Riemann zeta with 1/2 < beta = Re(rho) < 1. Its "
                        + "analytic multiplicity m is positive. Write D(x) = sqrt(x) log(x) and "
                        + "Jpsi(x) = weightedTail(psiErrorKernel, x) for the exact weighted tail. "
                        + "For every 0 <= c < m/(norm(rho) norm(rho-1)) and every real T, some "
                        + "u > max(T, log(2)) satisfies c < -exp((1/2-beta)u) D(exp(u)) Jpsi(exp(u)).")),
                    Paragraph(Text(
                        "CriticalThetaTailPeak supplies arbitrarily late positive peaks of the actual "
                        + "signed theta tail at the full coefficient from the pole at rho-1. The tail "
                        + "substitution gives f(u) = S(exp(u)) - Jpsi(exp(u)), where S is the "
                        + "activation-weighted integral of psi-theta. The prime-power comparison with "
                        + "sqrt(t) and the bound A(x) <= 2/D(x) give a uniform upper bound on D(x) S(x) "
                        + "for x >= 2. At beta > 1/2 the scaled upper bound tends to zero. Taking a "
                        + "theta peak at an intermediate coefficient leaves enough room for this error."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rh-of-eventually-normalized-weighted-tail-lower"),
                DeclarationHandle.Create(Prefix + "rh_of_eventually_normalized_weighted_tail_lower"),
                H("An eventual constant lower bound implies the Riemann hypothesis"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Suppose there is a real C with -C <= D(x) weightedTail(psiErrorKernel, x) "
                        + "for all sufficiently large real x. A zero in the open right half-strip "
                        + "would force a negative excursion at half its positive coefficient, while "
                        + "the eventual bound at x = exp(u) bounds the negative excursion above by "
                        + "C exp((1/2-beta)u), which tends to zero. RightHalfStripRiemannReduction "
                        + "then gives the Riemann hypothesis from exclusion of these zeros."))),
                DescribeRole.Theorem))));
}
