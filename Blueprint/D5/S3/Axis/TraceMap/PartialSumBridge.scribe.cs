using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Axis.TraceMap;

internal sealed class PartialSumBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var K = Id("K");

        var bridge = Equal(
            Call("wordSum", Call("shiftedWeight"), K),
            Call("axisPartialSum", Add(K, Num(1))));

        const string declarationPrefix = "D5/S3/Axis/TraceMap/PartialSumBridge.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "The admissible-word sum and the Zeckendorf-range sum agree under one depth shift.",
            H("Partial Sum Bridge"),
            Blocks(
                Paragraph(Text(
                    "Two formalizations of the same partial sum exist in this repository, "
                        + "written eight days apart under different index conventions. One sums "
                        + "over the subsets of an initial segment that contain no two adjacent "
                        + "indices, weighting each index one above its position. The other sums "
                        + "over an initial segment of the naturals, weighting each by the "
                        + "product over its Zeckendorf indices, which start at two.")),
                Paragraph(Text(
                    "They are not interchangeable as written: the depths differ by one and so do "
                        + "the weight indices. Numerical probes showed the two shifts before this "
                        + "theorem existed; the theorem is what makes a statement about one side "
                        + "a statement about the other.")),
                Paragraph(Text(
                    "The proof builds no Zeckendorf bijection. Both sides already carry the same "
                        + "two step recursion as public theorems and their two base values agree, "
                        + "so strong induction closes it. The two frozen modules the bridge spans "
                        + "are untouched.")),
                Describe.Lean(
                    DescribeId.Create("the-two-partial-sums-agree-under-both-shifts"),
                    DeclarationHandle.Create(
                        declarationPrefix + "wordSum_eq_axisPartialSum"),
                    H("The two partial sums agree under both shifts"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(bridge)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Shifting the weight index by two and the depth by one carries one sum "
                            + "onto the other. Cutting either shift makes the module fail to "
                            + "build, so both carry weight."))),
                    DescribeRole.Theorem))));
    }
}
