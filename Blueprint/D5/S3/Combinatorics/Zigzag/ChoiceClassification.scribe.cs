using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Zigzag;

internal sealed class ChoiceClassificationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Zigzag/ChoiceClassification.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Interior balance is local: future classes cannot alter retired vertices, and the six live residues distinguish the admissible labelled transitions.",
        H("Local Classification of Labelled Choices"),
        Blocks(
            Describe.Lean(DescribeId.Create("future-edges-miss-retired-vertices"),
                DeclarationHandle.Create(Prefix + "edgeFlow_future_zero"),
                H("Future edges miss both retired residues"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Under 3<=j<k<=n-j, an edge of class k has zero contribution at j-1 and its negative. The proof checks every one of the six source endpoint formulas using integer representatives and the ZMod distinctness criterion. This is the reason a later choice cannot repair a failed old balance equation."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("six-distinct-frontier-residues"),
                DeclarationHandle.Create(Prefix + "frontierVertex_injective"),
                H("The strict interior frontier is distinct"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "When 3<=j and 2j<n, the residues 1, -1, j-1, 1-j, j, -j are pairwise distinct. This permits the local flow equations to be read independently. The strict inequality deliberately excludes the parity boundary, which Retirement handles separately."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("local-balance-forces-table"),
                DeclarationHandle.Create(Prefix + "transition_labels_of_local_balance"),
                H("Local balance forces a listed transition"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The residual charge at each just-retired residue determines the allowed low and high form pair for the next state. The proof uses the complete finite form table in both signs; this converse classification is needed to decode arbitrary balanced choices, not only to verify paths already built."))),
                DescribeRole.Theorem)), []));
}
