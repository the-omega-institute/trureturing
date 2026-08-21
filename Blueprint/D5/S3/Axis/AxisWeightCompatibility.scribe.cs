using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Axis;

internal sealed class AxisWeightCompatibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var x = Id("x");
        var y = Id("y");
        var K = Id("K");

        var identification = Equal(
            Call("t", K),
            Call("t", K));

        var transported = Equal(
            Call("t", Add(K, Num(2))),
            Multiply(Call("t", Add(K, Num(1))), Call("t", K)));

        const string declarationPrefix = "D5/S3/Axis/AxisWeightCompatibility.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "The two axis weights introduced in this repository denote the same function.",
            H("Axis Weight Compatibility"),
            Blocks(
                Paragraph(Text(
                    "The axis weight was introduced twice, eight days apart, in two different "
                        + "strata. Both transcribe the same source formula, reading the "
                        + "expansion face against a golden power and the contraction face "
                        + "against the conjugate power at the same index. They differ only in "
                        + "where the negation sits, so they denote one function.")),
                Paragraph(Text(
                    "This document exists because the duplication was found the expensive way. "
                        + "The container the second family was written for already carried a "
                        + "formalization receipt naming the first family, and nothing carried "
                        + "that pointer to the person doing the work; the conflict surfaced "
                        + "only at deposit, after eight modules had been written and frozen.")),
                Paragraph(Text(
                    "What is identified here is the weight and nothing else. The two partial "
                        + "sums built on it are not equal: one indexes its words from one, the "
                        + "other runs over Zeckendorf indices starting at two. They range over "
                        + "the same combinatorial family under a shift of the index base, and "
                        + "the source pins no smallest index, so both readings are faithful. No "
                        + "equality between the two sums is asserted anywhere.")),
                Describe.Lean(
                    DescribeId.Create("the-two-axis-weights-are-one-function"),
                    DeclarationHandle.Create(declarationPrefix + "axisWeight_eq"),
                    H("The two axis weights are one function"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(identification)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Unfolding both definitions leaves two exponentials whose exponents "
                            + "differ by moving a negation across a product, which the ring "
                            + "normaliser discharges."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("the-recurrence-transports-across-the-identification"),
                    DeclarationHandle.Create(declarationPrefix + "axisWeight_succ_succ_transported"),
                    H("The recurrence transports across the identification"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(transported)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Rewriting along the identification carries the multiplicative "
                            + "Fibonacci law from one side to the other, so the two recorded "
                            + "recurrences are one fact about one object rather than two "
                            + "independent facts about two."))),
                    DescribeRole.Theorem))));
    }
}
