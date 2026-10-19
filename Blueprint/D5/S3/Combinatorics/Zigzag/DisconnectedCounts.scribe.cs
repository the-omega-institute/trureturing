using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Zigzag;

internal sealed class DisconnectedCountsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Zigzag/DisconnectedCounts.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every natural r at least one, each native disconnected-choice count is 4*(2^(r-1)-1).",
        H("The Two Native Disconnected Counts"),
        Blocks(
            Paragraph(Text("The objects retain every original class and Form label. Balance is integer balance at nonzero residues. Connectivity is weak connectivity on the actual active endpoints of the selected edges. Reflection supplies a second labelled sector; it does not identify choices.")),
            Describe.Lean(DescribeId.Create("excluded-initial-word"),
                DeclarationHandle.Create(Prefix + "DisconnectedCode"), H("The exact word fiber"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A code consists of an initial Boolean b and an absolute successor word w of length l. Only the word equal everywhere to b is removed. For positive length, the word equal everywhere to the opposite bit remains allowed."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("even-disconnected-equivalence"),
                DeclarationHandle.Create(Prefix + "evenDisconnectedChoicesEquiv"), H("Even native choices and both sectors"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every r at least one, the subtype of Choices (2*r) satisfying Balanced and failure of ActiveConnected is equivalent to the disjoint sum of two copies of DisconnectedCode (r-1). The positive native decoder realizes the first copy, and its zero-charge reflection realizes the second. Actual edge separation recovers the word from any disconnected balanced choice. Native code injection and reflection injection give uniqueness. The equivalence carries both inverse identities on the literal subtypes, including the antipodal cap."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("odd-disconnected-equivalence"),
                DeclarationHandle.Create(Prefix + "oddDisconnectedChoicesEquiv"), H("Odd native choices and the singleton cap"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every r at least one, the subtype of Choices (2*r+1) satisfying Balanced and failure of ActiveConnected has the same two-sector code type. The odd native decoder and its inverse retain the singleton cap and every label. Reflection preserves support at the same vertices. Both inverse identities belong to the equivalence."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("even-count"),
                DeclarationHandle.Create(Prefix + "disconnectedCount_even"), H("The even all-r formula"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural r with 1 <= r, disconnectedCount (2*r) = 4*(2^(r-1)-1). The literal filtered finite set has the cardinality of the native disconnected subtype. Each initial bit excludes one word from a function type of cardinality 2^(r-1); two bits and two labelled sectors supply the factor four."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("odd-count"),
                DeclarationHandle.Create(Prefix + "disconnectedCount_odd"), H("The odd all-r formula"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural r with 1 <= r, disconnectedCount (2*r+1) = 4*(2^(r-1)-1). Cardinality is transported through the odd native equivalence. At r=1 the empty word equals the constant initial word for either bit, so both code fibers and both counts are zero."))), DescribeRole.Theorem)), []));
}
