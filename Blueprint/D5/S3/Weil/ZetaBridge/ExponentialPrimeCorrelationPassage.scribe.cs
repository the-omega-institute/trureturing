using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class ExponentialPrimeCorrelationPassageDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common literal exponential envelope pays passage through the complete arithmetic Weil correlation.",
        H("Pass the complete prime-power correlation to the limit"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complete-prime-correlation-tendsto"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/ZetaBridge/ExponentialPrimeCorrelationPassage."
                    + "complete_prime_correlation_tendsto"),
                H("Both signed logarithmic samples and every prime power"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a sequence of continuous complex tests converge pointwise to a "
                        + "continuous test, with one common nonnegative A bounding their norms "
                        + "by A exp(-|x|). The complete Mangoldt series of the original Weil "
                        + "self-correlation is summable for every sequence member and for its "
                        + "limit, and the entire series converges. Both correlation samples "
                        + "at log n and -log n remain, with the actual Lambda(n)/sqrt(n) "
                        + "coefficient. Evenness is not required.")),
                    Paragraph(Text(
                        "The triangle inequality gives a product majorant with an "
                        + "exp(-3|s|/4) shift factor and an integrable exp(-|x|/4) spatial "
                        + "factor. Integral dominated convergence gives the correlation "
                        + "limit at each shift. The arithmetic envelope is then a constant "
                        + "times Lambda(n)n^(-5/4); its summability is supplied by Mathlib's "
                        + "actual von Mangoldt L-series theorem in Re(s)>1. Tannery's "
                        + "dominated-series theorem pays the complete arithmetic limit.")),
                    Paragraph(Text(
                        "This supplies the prime side of a noncompact signed Weil passage "
                        + "for the compact theta-cusp approximations and their finite complex "
                        + "combinations once their literal common envelope and pointwise "
                        + "limit are inserted. Gamma, pole, zero-side and original-source "
                        + "identification remain separate obligations. The result asserts "
                        + "neither an explicit formula nor positivity or RH. Classical "
                        + "dominated convergence and the L-series supplier are reused, "
                        + "without a literature-priority claim."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Weil/ZetaCore/ExplicitFormula"))
        ]));
}
