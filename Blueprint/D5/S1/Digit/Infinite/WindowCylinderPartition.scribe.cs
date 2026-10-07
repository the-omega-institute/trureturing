using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class WindowCylinderPartitionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Cylinder Partition of Legal Digit Windows.",
        H("The Cylinder Partition of Legal Digit Windows"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("windowcylinderpartition-prepend-digits"),
                DeclarationHandle.Create("D5/S1/Digit/Infinite/WindowCylinderPartition.prepend_digits"),
                H("Digits of a prepended return-block word"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every finite return-block word w, legal tail y and natural index j, "
                    + "the j-th digit of prependWord w y is the j-th expanded digit of w "
                    + "when j is less than len w. At every later index it is the digit of y "
                    + "at j minus len w. This identifies the prefix and tail in each "
                    + "window cylinder."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("windowcylinderpartition-window-cylinder-partition"),
                DeclarationHandle.Create("D5/S1/Digit/Infinite/WindowCylinderPartition.window_cylinder_partition"),
                H("Closed intervals and oriented circle cuts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Complete a legal window by appending a zero when its last digit is one. "
                    + "The resulting return-block word parametrizes its cylinder by arbitrary legal tails. "
                    + "The signed values form a closed affine interval of length alpha to the completed "
                    + "digit length. For each positive window length these intervals cover the full value "
                    + "range and have pairwise disjoint interiors. Their circle boundaries are precisely "
                    + "the negative golden phases indexed from one through the Fibonacci window count. "
                    + "Each cylinder contains the full preimage of its open arc, the positive-side stream "
                    + "at its left endpoint, and the negative-side stream at its right endpoint. "
                    + "The two streams at an indexed phase have different windows exactly when the index "
                    + "does not exceed the window count. At the circle seam the positive and negative "
                    + "streams are the lower and upper alternating streams, respectively."))),
                DescribeRole.Theorem))));
}
