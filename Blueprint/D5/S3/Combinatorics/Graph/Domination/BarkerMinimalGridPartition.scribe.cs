using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;
internal sealed class BarkerMinimalGridPartitionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPartition.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal partition covers every full state and carries terminal vectors and all 64 starts to the exact 59-class quotient.", H("The total transfer partition"), Blocks(
            N("classOf", "The total partition", "Every one of the 4672 full states maps to its literal class in Fin 59, using 73 literal pages of 64 entries indexed by all 4672 state values. Unreachable states remain included.", DescribeRole.Definition),
            N("successors", "Every admitted successor", "The list contains the class of append s m once for every accepted real mask m.", DescribeRole.Definition),
            N("quotientSuccessors", "Expanded quotient rows", "The sparse integer weight of each quotient row entry is expanded into that many copies of its destination class.", DescribeRole.Definition),
            N("row_certificate", "Every full row", "For every full state s, the complete admitted-successor class list is a permutation of its expanded quotient row. This verifies all destinations and multiplicities without restricting to reachable states.", DescribeRole.Theorem),
            N("terminal_certificate", "Every full terminal weight", "For every full state s, the full terminal weight equals the quotient terminal value at classOf s.", DescribeRole.Theorem),
            N("alpha", "The initial quotient row", "The 59 exact initial class multiplicities retain all 64 labelled two-column starts.", DescribeRole.Definition),
            N("initialClasses", "Every initial class", "The class list enumerates the first 64 full states in order.", DescribeRole.Definition),
            N("alphaClasses", "Expanded initial row", "The alpha entry at each quotient class is expanded into its stated multiplicity.", DescribeRole.Definition),
            N("initial_certificate", "All initial multiplicities", "The 64 initial classes are a permutation of alphaClasses, retaining every initial labelled pair exactly once.", DescribeRole.Theorem),
            Paragraph(Text("The row, terminal and initial multiset identities are checked against the actual transfer predicate for every full state. These finite identities connect the literal data to the all-length actual-subset counting argument."))), []));
    private static DocumentBlock N(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("bpt-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
