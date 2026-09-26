using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Zigzag;

internal sealed class ChoicesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Zigzag/Choices.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/feldman2026missingzigzag");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The counted objects are Feldman's labelled choices with balance at every nonzero residue, without a closedness or connectivity restriction.",
        H("Literal Zigzag Choices and Balance"),
        Blocks(
            Describe.Lean(DescribeId.Create("six-directed-forms"),
                DeclarationHandle.Create(Prefix + "formPair"), H("Six labelled directed forms"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Section 5 equation (2) gives I=(1,k-1), II=(k,1-k), III=(-1,k), IV=(k-1,-k), V=(-k,1), and VI=(1-k,-1) in ZMod n. The Form index is retained independently of endpoints: coincident pairs never merge labels. This is a fresh transcription of the paper, compared with the author's formPair, without importing its code or certificates."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("admissible-choice-functions"),
                DeclarationHandle.Create(Prefix + "Choices"), H("One form per class"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For n=3t the index Fin (3t-3) represents exactly k=2 through n-2. The subtype admits only II, III, IV, or V at the first class and retains all six labels thereafter. No endpoint distinctness, step-sum closure, or cyclic order is imposed."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("balance-only-predicate"),
                DeclarationHandle.Create(Prefix + "Balanced"), H("Balance at nonzero residues"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The integer imbalance sums outgoing minus incoming incidences of every selected edge. Balanced requires that sum to vanish at each nonzero ZMod residue, leaving the zero residue untested as in the source. It does not assert a closed path, connected graph, Eulerian circuit, or Hamiltonian cycle."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-balanced-cardinality"),
                DeclarationHandle.Create(Prefix + "balancedCount"), H("The actual count a(t)"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "This is the cardinality of the finite filter on Choices t satisfying Balanced. Every later path polynomial is linked back to this exact finite set by both parity equivalences; it is never substituted for a proxy count."))),
                DescribeRole.Definition)), []));
}
