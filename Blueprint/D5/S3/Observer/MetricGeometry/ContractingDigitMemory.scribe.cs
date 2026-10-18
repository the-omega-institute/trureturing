using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometry;

internal sealed class ContractingDigitMemoryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary contracting digits have an exact finite-state accuracy law.",
        H("Contracting Digit Memory"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("contracting-digit-memory-exact"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/ContractingDigitMemory."
                    + "contracting_digit_memory_exact"),
                H("The exact state count for contracting binary digits"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let the contraction parameter lambda be positive and less than one half. "
                        + "Encode every infinite binary stream as the real number obtained from "
                        + "the normalized geometric digit series, and let an action prepend a bit "
                        + "to the stream. For an integer L at least one and an error epsilon at least "
                        + "lambda to the power L divided by two and strictly less than (1 minus lambda) times lambda "
                        + "to the power L minus one divided by two, the least number of states of a "
                        + "finite predictor with this readout and action is exactly 2 to the power L.")),
                    Paragraph(Text(
                        "The upper bound stores the first L bits. Each action inserts its bit at the "
                        + "front and drops the last stored bit. Each prefix class lies in an interval "
                        + "of length lambda to the power L, so its midpoint gives error at most half that length.")),
                    Paragraph(Text(
                        "For the lower bound, the 2 to the power L zero-tail prefixes are separated "
                        + "by at least (1 minus lambda) times lambda to the power L minus one. Two "
                        + "such prefixes mapped to one finite state would therefore incur total error "
                        + "at least that separation, contradicting the strict upper error bound. The "
                        + "special value epsilon equal to lambda to the power L divided by two gives "
                        + "the same exact state count for arbitrarily long action words.")),
                    Paragraph(Text(
                        "For every positive error epsilon, define N(epsilon) as the least natural "
                        + "budget for this same predictor predicate, with all initial states and all finite "
                        + "action words. Geometric radii tend to zero, so an exact-window predictor at a "
                        + "sufficiently small radius is feasible at epsilon. The nonempty set of feasible "
                        + "natural budgets therefore has a minimum. A witness at that minimum has "
                        + "exactly N(epsilon) states: its own cardinality is another feasible budget, "
                        + "so minimality and its budget bound force equality. Nonempty finite machines "
                        + "have positive cardinality, which also excludes the zero budget.")),
                    Paragraph(Text(
                        "Increasing the permitted error preserves every original full-future error "
                        + "inequality of a predictor. Thus N(epsilon) decreases as the positive error "
                        + "increases. For 0 < epsilon < one half, choose n at least zero with lambda to "
                        + "the power n plus one strictly less than twice epsilon and twice epsilon at "
                        + "most lambda to the power n. The existing exact geometric counts and this "
                        + "monotonicity give 2 to the power n at most N(epsilon) at most 2 to the power "
                        + "n plus one; when n is zero the lower bound is positivity of the minimum.")),
                    Paragraph(Text(
                        "Write a = log(1/lambda), c = log 2 and T = log(1/epsilon). Both a and T are "
                        + "positive in the stated range. Taking logarithms of the neighboring-scale "
                        + "bounds places log N(epsilon) between n times c and (n plus one) times c, "
                        + "and places T minus c between n times a and (n plus one) times a. Consequently "
                        + "log N(epsilon) divided by T lies between c/a minus (c plus c squared/a)/T "
                        + "and c/a plus (c plus c squared/a)/T. As epsilon tends to zero through all "
                        + "positive real values, T tends to infinity and both bounds tend to "
                        + "log 2 divided by log(1/lambda). This is the full one-sided limit.")),
                    Paragraph(Text(
                        "For phi = (1 + sqrt 5)/2, the identity phi squared = phi + 1 and phi > 1 "
                        + "give 0 < 1/phi squared < one half. Substitution in the same exact-window "
                        + "theorem gives N(1/(2 phi to the power 2L)) = 2 to the power L for every "
                        + "integer L at least one, including L = 1 and equality at the weak lower "
                        + "radius endpoint. Since log(1/(1/phi squared)) = 2 log phi > 0, the full "
                        + "complexity exponent is log 2 divided by (2 log phi). These are consequences "
                        + "for the specified affine digit dynamics and scalar readout; they assert "
                        + "neither physical storage costs nor a priority claim for Cantor-set exponents."))),
                DescribeRole.Theorem))));
}
