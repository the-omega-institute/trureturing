using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeSelectedCInvariantDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeSelectedCInvariant.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Classify Every Retained and New Native c Edge.",
        H("Classify Every Retained and New Native c Edge"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-selected-cinvariant-native-special-path-c-labels"), DeclarationHandle.Create(Prefix + "native_special_path_c_labels"),
                H("Special Joining Adds Only a Newly Selected c Label"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Given the exact uncut-piece inventory of one previous special cycle and the literal native port coordinates of the joined piece finishes, every c edge of the actual joined special path has a terminal among the previous selected labels or the supplier terminal. Old edges and newly inserted seams are handled separately."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-selected-cinvariant-native-other-path-c-labels"), DeclarationHandle.Create(Prefix + "native_other_path_c_labels"),
                H("An Ordinary Opening Adds No Edge"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An ordinary child path with the exact one-supplier-cut complement inventory inherits the supplied previous cycle classification of c edges. The conclusion concerns every actual edge of the chosen complement path."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-selected-cinvariant-native-parent-cycle-c-labels"), DeclarationHandle.Create(Prefix + "native_parent_cycle_c_labels"),
                H("Exhaust Every c Edge of the Same Parent Cycle"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complete literal parent edge chain consists of the actual lifted child-path edges and its outer seams. Supplied classifications for those same child paths imply that every c edge of this parent cycle has a terminal among the old selected labels or the supplier terminal. The child association, root coordinate and chain inventory remain explicit premises."))), DescribeRole.Theorem))));
}
