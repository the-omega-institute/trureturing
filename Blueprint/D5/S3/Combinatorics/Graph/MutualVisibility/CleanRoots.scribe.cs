using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.MutualVisibility;

internal sealed class CleanRootsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/fresanfigueroa2026mutualvisibility");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Auxiliary cut structure for full mutual-visibility reconfiguration.",
        H("CleanRoots"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-clean-root"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/MutualVisibility/CleanRoots.exists_cleanRoot"),
                H("A clean root exists"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A configuration cut smaller than the host order leaves a label whose singleton survives and for which no cut member has exactly that label outside the deleted-singleton labels."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("deleted-labels"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/MutualVisibility/CleanRoots.deletedLabels"),
                H("Deleted singleton labels"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The finite host labels whose singleton configurations belong to the fixed cut."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("clean-root"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/MutualVisibility/CleanRoots.CleanRoot"),
                H("One clean surviving root"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The label is outside the deleted singleton labels, and every member of the same cut has outside support different from that singleton label."))),
                DescribeRole.Definition),
            Paragraph(Text("Deleted labels are those whose singleton configurations belong to one fixed cut. A clean root is a surviving label for which no cut configuration has that label as its entire support outside the deleted labels. If a cut has fewer members than the host has labels, at least one clean root exists: singleton cuts pay deleted labels, while disjoint one-label outside supports pay all other dirty labels. For a pair on deleted labels in a component separated from the clean root singleton, a feasible triple containing that root would give an uncut TAR path to the root. A host edge from a pair endpoint to the root would likewise give an uncut slide followed by deletion. Thus such triples are not visible and both endpoint-to-root host edges are absent. Mandatory root separation is excluded by a maximal pair-complete configuration and the sparse-slide degree bound. The minimum-pair degree count combines these exclusions with simultaneous inward payments to obtain the full separator conclusion.")))));
}
