using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeActualInductionStateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualInductionState.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual induction state retains one supplied cycle and all data later consumed by the native recursion.",
        H("The Complete Actual Induction State"),
        Blocks(
            Describe.Lean(DescribeId.Create("state-for"), DeclarationHandle.Create(Prefix + "StateFor"),
                H("One Cycle with Both Literal Boundary Orders"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a supplied frame, the state contains one actual Hamilton cycle in its marked domain, two disjoint cut groups with their exact native images, a joint partition and both restored partitions on that cycle. It records each distinguished endpoint as a literal port coordinate, the primary and opposite parity flags, and the retained protected-a, remaining-b and selected-c edge conditions. Its opposite frame is the canonical selected-order exchange. This structure specifies the data required by the recursion; existence is proved by the separate all-order construction."))), DescribeRole.Definition))));
}
