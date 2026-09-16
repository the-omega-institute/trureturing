using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Separator;

internal sealed class LiteralRationalBoundaryGridDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Separator/LiteralRationalBoundaryGrid.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact rational cutoff and exponential enclosures feed a signed dyadic grid for "
            + "the literal same-H pole-boundary computation.",
        H("Literal Rational Pole-Boundary Grid"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cutoff-certified"),
                DeclarationHandle.Create(Prefix + "cutoffCertified"),
                H("Certified rational smooth-transition enclosure"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For t at or below zero the result is exactly depth zero and [0,0]; "
                        + "for t at or above one it is exactly depth zero and [1,1]. For "
                        + "an interior rational t, finite search retains the first Taylor "
                        + "depth satisfying the rational predicate, both denominator and "
                        + "reciprocal checker calls, a signed enclosure of smoothTransition, "
                        + "and the requested dyadic width. The analytic proof fields are erased."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("boundary-exp-certified-v1"),
                DeclarationHandle.Create(Prefix + "boundaryExpCertified_v1"),
                H("First certified signed exponential enclosure"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every rational exponent and natural precision, the definition "
                        + "returns the first positive Taylor depth accepted by the guard. "
                        + "Its actual rational Taylor interval encloses the real exponential, "
                        + "may have signed endpoints, and has width at most the requested "
                        + "dyadic tolerance."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rational-interval-mul-bounds"),
                DeclarationHandle.Create(Prefix + "rationalIntervalMul_bounds"),
                H("Signed four-corner interval multiplication"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The product interval takes the minimum and maximum of all four endpoint "
                        + "products. For ordered signed input intervals with amplitude caps, "
                        + "it remains ordered, inherits the product amplitude cap, and obeys "
                        + "the first-order width estimate A*width(b)+B*width(a). No positivity "
                        + "assumption is imposed on either input interval."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rational-interval-square-width"),
                DeclarationHandle.Create(Prefix + "rationalIntervalSquare_width"),
                H("Completed-square width across every sign branch"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Squaring uses the lower endpoint squared on a nonnegative interval, the "
                        + "upper endpoint squared on a nonpositive interval, and lower endpoint "
                        + "zero when the interval crosses zero. All three branches satisfy the "
                        + "same twice-cap-times-width estimate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("boundary-grid"),
                DeclarationHandle.Create(Prefix + "boundaryGrid"),
                H("Computed dyadic grid for the literal family"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For radius R, rational polynomials p and q, mesh depth k, and scalar "
                        + "depth s, this definition computes all cutoff and positive/negative "
                        + "exponential node enclosures and both families of checked cell "
                        + "expressions. The cell arithmetic keeps signed four-corner products; "
                        + "the final completed-square construction keeps the zero-crossing "
                        + "branch. The arrays are the concrete grid consumed by the semantic "
                        + "and rate certificates."))),
                DescribeRole.Definition),
            Paragraph(Text(
                "This module constructs rational ingredients for one literal same-H witness. "
                    + "It does not certify compact, prime, or Archimedean intervals, assert an "
                    + "off-line zero, extract a negative witness, or prove the Riemann hypothesis."))),
        []));
}
