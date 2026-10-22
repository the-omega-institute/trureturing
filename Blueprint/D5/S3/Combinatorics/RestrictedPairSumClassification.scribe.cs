using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class RestrictedPairSumClassificationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RestrictedPairSumClassification.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/costa2026smallabelian");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The corrected finite restricted-pair-sum classification for arbitrary abelian groups.",
        H("Restricted pair sums and additive stabilizers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("restricted-pair-sum-classification"),
                DeclarationHandle.Create(Prefix + "restricted_pair_sum_classification"),
                H("At least three nonzero elements force a subgroup carrier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For a finite A in an arbitrary AddCommGroup with 0 outside A and "
                    + "cardinality at least three, every sum of distinct elements of A in "
                    + "insert 0 A is equivalent to insert 0 A being the carrier of an "
                    + "additive subgroup carrier. The elementary converse is not "
                    + "formalized in this module. The proof is the finite translation and "
                    + "translation-stabilizer argument. The source's k >= 2 boundary is "
                    + "false: A={1,4} in Z/5Z is the C5 counterexample. In the original "
                    + "quotient, the contrapositive preserves the same Q and total under a "
                    + "pair merge, but a split interval at the expanded block's internal "
                    + "cut leaves the ordering expansion unresolved.")),
                DescribeRole.Theorem))));
}
