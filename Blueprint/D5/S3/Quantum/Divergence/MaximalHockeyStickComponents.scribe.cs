using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class MaximalHockeyStickComponentsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive matrix components construct one actual finite reverse test with its entire hockey profile.",
        H("Actual reverse tests from positive components"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("maximal-hockey-components-profile"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Divergence/MaximalHockeyStickComponents."
                        + "reverse_test_from_components_profile"),
                H("The same test realizes the cost and every threshold"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/hiaimosonyitomamichel2026hockeystick")),
                Blocks(Paragraph(Text(
                    "For positive components G_i and 0 <= x_i <= 1, the construction prepares "
                        + "the two sums x_i G_i and (1-x_i) G_i with actual density states. "
                        + "Its quadratic cost and its classical hockey profile at every real "
                        + "threshold are computed from those same labels. Zero components "
                        + "have zero classical mass, and an empty carrier uses no labels."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("maximal-hockey-components-reverse-test-from-components"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/MaximalHockeyStickComponents.reverse_test_from_components"),
                H("The cost projection of the actual component construction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/hiaimosonyitomamichel2026hockeystick")),
                Blocks(Paragraph(Text("For PSD G_i indexed by the matrix index n and x_i in [0,1], an actual test with card(n) labels prepares sum x_i G_i and sum (1-x_i)G_i with the stated quadratic cost sum (2x_i-1)^2 Tr(G_i). This projection of reverse_test_from_components_profile is an organization helper, not separate new mathematics."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("maximal-hockey-components-reverse-test-from-weighted-components"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/MaximalHockeyStickComponents.reverse_test_from_weighted_components"),
                H("Independent finite component labels"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/hiaimosonyitomamichel2026hockeystick")),
                Blocks(Paragraph(Text("For an arbitrary finite label type l independent of the matrix index n, PSD components G_i, arbitrary nonnegative coefficients a_i,b_i and a coordinate map l -> n, the construction gives an actual test with card(l) labels preparing sum a_i G_i and sum b_i G_i. At every real t its actual hockey profile is sum max(a_i-t b_i,0) Tr(G_i). The coordinate supplies a density state only for zero components; no Nonempty n is imposed. Operational.reverse_test_attains_hockey consumes it with Fin 3 labels when n is nonempty, while the empty case uses an empty test."))), DescribeRole.Theorem))));
}
