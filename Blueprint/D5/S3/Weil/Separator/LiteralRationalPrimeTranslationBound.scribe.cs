using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Separator;

internal sealed class LiteralRationalPrimeTranslationBoundDocument
    : IScribeDocumentDefinition
{
    private const string Result =
        "D5/S3/Weil/Separator/LiteralRationalPrimeTranslationBound."
        + "literal_rational_prime_translation_bound";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit rational coefficient budgets give a global translation-energy modulus for "
            + "the exact literal smooth-transition Weil test.",
        H("Literal Rational Translation-Energy Modulus"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("literal-rational-prime-translation-bound"),
                DeclarationHandle.Create(Result),
                H("A global modulus from finite coefficient budgets"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For positive natural radius R and rational polynomials p and q, "
                            + "coefficientBudget sums the absolute coefficients weighted at "
                            + "B=2R. The resulting rational quantities A and D bound the "
                            + "values and derivatives of the real and imaginary even "
                            + "polynomial components throughout the support interval.")),
                    Paragraph(Text(
                        "The proof derives an explicit derivative bound for expNegInvGlue and "
                            + "then proves that smoothTransition has derivative between zero "
                            + "and nine. This gives a global nine-Lipschitz estimate. Together "
                            + "with exact vanishing at both endpoints, support-crossing "
                            + "arguments extend the local polynomial estimates to a global "
                            + "amplitude bound A and Lipschitz constant "
                            + "K=D+(9/R)A for the exact literal function.")),
                    Paragraph(Text(
                        "Translation energy is rewritten as mass minus twice a correlation. "
                            + "The difference of two correlations is localized to the union "
                            + "of their translated support intervals, whose measure is at most "
                            + "8R. Integrating the pointwise A*K*|s-t| comparison yields "
                            + "|translationEnergy f s-translationEnergy f t| at most "
                            + "32*R*A*K*|s-t| for all real shifts s and t.")),
                    Paragraph(Text(
                        "The function f is required pointwise to equal the same literal "
                            + "smoothTransition(2-|y|/R)*rationalEvenPolynomial(p,q,y) used by "
                            + "the existing off-line-zero witness. This result transfers a "
                            + "certified shift width into an energy error bound. It does not "
                            + "enclose log n or square-root weights, aggregate the complete "
                            + "activePrimePowers set, certify a negative full-energy witness, "
                            + "assert an off-line zero, or prove the Riemann hypothesis."))),
                DescribeRole.Theorem)),
        []));
}
