using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.MutualVisibility;

internal sealed class PairPaymentsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/MutualVisibility/PairPayments.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/fresanfigueroa2026mutualvisibility");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Auxiliary finite cut-counting structure for mutual-visibility reconfiguration.",
        H("PairPayments"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("minimal-pair-exists"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/MutualVisibility/PairPayments.minimal_pair_exists"),
                H("A minimum rooted pair exists"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For a nonempty family of distinct pairs reachable from one configuration after one cut, there is a pair minimizing the sum of endpoint distances to a fixed root."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("simultaneous-inward-payments"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/MutualVisibility/PairPayments.simultaneous_inward_payments"),
                H("Exceptional triples have simultaneous disjoint payments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Fix a minimum rooted pair, its dominating orientation, and one inward predecessor. Every selected label adjacent to both endpoints with a visible triple in the same surviving component supplies one distinct member of the actual cut. These payments avoid the internal class and every class with a single outside label."))),
                DescribeRole.Theorem),

            Describe.Lean(
                DescribeId.Create("local-cut-class"),
                DeclarationHandle.Create(Prefix + "localCutClass"),
                H("Cut classes for one outside label"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Take members of one cut which contain the designated label and have no other label outside the fixed base. Classes for distinct labels outside the base are disjoint."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-cut-budget"),
                DeclarationHandle.Create(Prefix + "joint_cut_budget"),
                H("One simultaneous cut budget"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Fix one cut, one base, a finite family of labels outside the base, and a further family F of cut members. Assume F is disjoint from the internal cut class and from every selected local class. The cardinality of the internal class, the sum of the local cardinalities, and the cardinality of F together are at most the cardinality of that same cut. The proof takes their disjoint union and includes it into the actual cut.")))),
            Paragraph(Text("Choose a pair of minimum root-distance sum in one actual surviving component. Every exceptional visible common-neighbor triple has an inward slide followed by a deletion to a pair of smaller sum, so one intermediate configuration is in the same cut. With one common predecessor p, its labels outside the original pair are exactly p and the exceptional label y. This distinguishes payments for different labels and separates them from every local cut class with just one outside label. A disjoint-union cardinality bound combines these payments with the internal and local classes. The cyclic high-rank cut bound, singleton-core connection, clean-root existence and clean-root pair exclusions are auxiliary results. The maximal sparse-slide argument establishes rooted comparability. The minimum-pair local count combines these payments with the singleton core and high-rank component bound to obtain the full separator equality.")))));
}
