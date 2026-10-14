using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeRecursiveCycleStepDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveCycleStep.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Recursive Parent Cycles and Their Chosen Children.",
        H("Actual Recursive Parent Cycles and Their Chosen Children"),
        Blocks(
            Describe.Lean(DescribeId.Create("recursive-cycle-from-specified-children-with-inventory"), DeclarationHandle.Create(Prefix + "recursive_cycle_from_specified_children_with_inventory"),
                H("Keep Every Supplied Ordinary Cycle Attached"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A Hamilton path on the special child and a specified Hamilton cycle on each ordinary child, including membership of its literal supplier cut, construct a full parent Hamilton cycle. Every ordinary opening has exactly the edge complement of its particular supplied child cycle, and the chosen pieces retain the exact parent support and edge identities."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("recursive-cycle-from-special-with-inventory"), DeclarationHandle.Create(Prefix + "recursive_cycle_from_special_with_inventory"),
                H("Choose Actual Ordinary Cycles Once"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A supplied special Hamilton path and existence of ordinary child cycles with their actual supplier cuts construct a full parent Hamilton cycle. The output records each chosen child cycle and the exact complement inventory of its opening, so later joint partitions remain attached to the cycles used by the construction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-recursive-even-cycle-step"), DeclarationHandle.Create(Prefix + "native_recursive_even_cycle_step"),
                H("Construct a Parent from an Actual Even State"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For k=2s+2, the supplied special Hamilton cycle, complete actual partition at special cuts and even boundary endpoints construct the special path. Together with genuine ordinary child cycles and their actual supplier-cut membership, these paths earn a full parent Hamilton cycle. Existence of the prior child cycles and their boundary state remains a hypothesis."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-recursive-odd-cycle-step"), DeclarationHandle.Create(Prefix + "native_recursive_odd_cycle_step"),
                H("Construct a Parent from an Actual Odd State"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For k=2s+3, the supplied special Hamilton cycle, complete actual partition at special cuts and odd boundary endpoints construct the special path. Together with genuine ordinary child cycles and their actual supplier-cut membership, these paths earn a full parent Hamilton cycle. This is a verified recursive constructor, not an unconditional all-size existence assertion."))), DescribeRole.Theorem))));
}
