using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure.Polylogarithm;

internal sealed class CompositionEventualNegativeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive finite composition and positive reciprocal power has strictly negative "
        + "ordinary coefficients beyond a parameter-dependent threshold.",
        H("CompositionEventualNegative"), Blocks(
            Describe.Lean(DescribeId.Create("eventual-strict-negative-coefficients"),
                DeclarationHandle.Create(
                    "D5/S3/AnalyticClosure/Polylogarithm/CompositionEventualNegative.result"),
                H("Strict eventual negativity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/AnalyticClosure/xu2026rational")),
                Blocks(
                    Paragraph(Text(
                        "For every head : PNat, tail : List PNat and ell : PNat, there is an integer "
                        + "N at least one such that CompositionReciprocalSeries.ordinaryCoefficient "
                        + "head tail ell n is strictly negative whenever n is at least N. "
                        + "These are the ordinary real coefficients of the inverse of the ell-th "
                        + "power of the actual normalized source series. The threshold may depend on "
                        + "all parameters. The statement includes an empty tail and every finite "
                        + "leading-one block.")),
                    Paragraph(Text(
                        "The actual zero-free collar and the same-power continuous conjugate banks "
                        + "give a finite radius R greater than one. In logarithmic coordinates the "
                        + "reciprocal extends continuously to a rectangle with real coordinates "
                        + "from log(1/2) to log R and imaginary coordinates from zero to 2 pi. "
                        + "The bottom and top traces are the upper and lower banks. Cauchy-Goursat "
                        + "on this rectangle identifies the small-circle coefficient integral with "
                        + "the outer vertical integral plus the bottom integral minus the top "
                        + "integral. Below zero the horizontal traces cancel; above zero their "
                        + "difference is 2 i times the imaginary part of the upper bank. "
                        + "This retains the positive sign of the bank contribution in the source "
                        + "coefficient formula, including both finite endpoints.")),
                    Paragraph(Text(
                        "Write b=log R and h(x) for minus the upper-bank imaginary part at exp x. "
                        + "Then h is continuous on [0,b], is zero at zero, and is strictly positive "
                        + "on (0,b]. Compactness bounds the outer error by B exp(-n b). "
                        + "On a fixed subinterval [alpha,beta] inside (0,b), h has a positive "
                        + "minimum. Its weighted integral is at least c exp(-n beta), with c "
                        + "positive. Since beta is less than b, geometric decay makes the outer "
                        + "error strictly smaller than this negative bank mass for all sufficiently "
                        + "large n. No uniform, least or effective threshold is asserted."))),
                DescribeRole.Theorem))));
}
