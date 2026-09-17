using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Admissibility;

internal sealed class WindowCapacityExtremaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Extremal Fibonacci Window Widths.",
        H("Extremal Fibonacci Window Widths"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("windowcapacityextrema-maximizer-has-extremal-shape"),
                DeclarationHandle.Create("D5/S1/Digit/Admissibility/WindowCapacityExtrema.maximizer_has_extremal_shape"),
                H("Necessary shapes of a maximizing width vector"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fix a positive number of registers and a nonnegative total width. "
                    + "If a width vector maximizes the product of Fibonacci window sizes among all "
                    + "vectors with that total width, then at or below the register count every width "
                    + "is zero or one. At or above the register count, every width except one is one, "
                    + "and the remaining width is the total minus the register count plus one. "
                    + "At equality of total width and register count both descriptions give all ones. "
                    + "Moving width from a coordinate of size at least two to a zero coordinate "
                    + "strictly increases the product, as does combining two widths of size at least "
                    + "two into their sum minus one and a width of one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("windowcapacityextrema-capacity-isgreatest-and-eq-iff"),
                DeclarationHandle.Create("D5/S1/Digit/Admissibility/WindowCapacityExtrema.capacity_isGreatest_and_eq_iff"),
                H("Exact capacity and all maximizing widths"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a positive number k of registers, the greatest product at total width B "
                    + "is 2 to the power B when B is at most k, and otherwise is 2 to the power "
                    + "(k - 1) multiplied by the Fibonacci window size at width B - k + 1. "
                    + "The greatest value is attained. A feasible vector attains it exactly when its "
                    + "widths have the stated extremal shape. The feasible vectors form a nonempty "
                    + "finite set, and evaluating the product on the maximizing shapes gives the formula. "
                    + "At zero budget the capacity is one; at budget k both formulas give 2 to the power k."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("windowcapacityextrema-state-product-le-capacity-and-eq-iff"),
                DeclarationHandle.Create("D5/S1/Digit/Admissibility/WindowCapacityExtrema.state_product_le_capacity_and_eq_iff"),
                H("Capacity bound and equality for register state counts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let each nonnegative register capacity be smaller than its Fibonacci window size, "
                    + "and let the sum of the widths be at most the budget. The product of the register "
                    + "capacities plus one is at most the exact window capacity. Equality holds if and "
                    + "only if the widths use the whole budget, have an extremal shape, and each register "
                    + "capacity is one less than its window size. Adding any unused budget to one width "
                    + "strictly increases the window product. All register state counts are positive, "
                    + "so a single unsaturated register also makes the product inequality strict."))),
                DescribeRole.Theorem))));
}
