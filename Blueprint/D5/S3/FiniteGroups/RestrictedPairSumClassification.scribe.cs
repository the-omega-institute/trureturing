using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class RestrictedPairSumClassificationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FiniteGroups/RestrictedPairSumClassification.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/costa2026smallabelian");

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
                    + "cardinality at least three, if every sum of distinct elements of A "
                    + "belongs to insert 0 A, then insert 0 A is the carrier of an "
                    + "additive subgroup. The elementary converse is not "
                    + "formalized in this module. The present finite translation and "
                    + "translation-stabilizer proof establishes the corrected form of "
                    + "Theorem 2.4 of Simone Costa, Stefano Della Fiore, Mattia Fontana "
                    + "and Lluís Vena, arXiv:2603.20961v1, with the lower bound "
                    + "k >= 3. The printed "
                    + "k >= 2 boundary is "
                    + "false: A={1,4} in Z/5Z is the C5 counterexample. In the original "
                    + "quotient Q, if insert 0 A is not a subgroup carrier, the "
                    + "contrapositive supplies distinct a,b with a+b outside insert 0 A. "
                    + "Replacing a,b by a+b decreases the cardinality by one and preserves "
                    + "distinctness, nonzeroness, the total and the same original Q. "
                    + "A split interval at the expanded block's internal cut leaves the "
                    + "ordering expansion unresolved. The universal ordering target with "
                    + "the same original M and coefficient one in the original coordinates "
                    + "remains open."))),
                DescribeRole.Theorem))));
}
