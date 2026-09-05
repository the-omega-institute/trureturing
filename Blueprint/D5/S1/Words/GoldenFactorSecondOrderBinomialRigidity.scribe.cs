using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class GoldenFactorSecondOrderBinomialRigidityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Words/GoldenFactorSecondOrderBinomialRigidity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two binomial counts faithfully identify each fixed-length consecutive golden factor.",
        H("Golden Factor Second-Order Binomial Rigidity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-factor-second-order-binomial-rigidity"),
                DeclarationHandle.Create(
                    Prefix + "golden_factor_eq_iff_second_order_profile_eq"),
                H("Second-order profile and complete factor have identical fibers"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a known length, count the true letters and scattered true-before-false pairs. Equality of these two counts is equivalent to equality of the consecutive golden factors.")),
                    Paragraph(Text(
                        "The proof reuses the frozen Beatty window-count formula. Rotation-intercept order compares all prefix counts in a common direction; their summed area is determined by the two binomial counts.")),
                    Paragraph(Text(
                        "Rigo and Salimov established the general Sturmian phenomenon in Theoretical Computer Science 601 (2015), pages 47-57. This node supplies the repository-specific formal bridge and does not claim mathematical novelty for the general result.")),
                    Paragraph(Text(
                        "The theorem recovers the factor word, not its absolute occurrence position. Arbitrary prime-golden event lists are outside this language restriction. The full signature-to-binomial representation adapter is a separate obligation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-factor-first-order-collision-witness"),
                DeclarationHandle.Create(Prefix + "legal_golden_first_order_collision"),
                H("An explicit legal collision at first order"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The factors at starts zero and one of length two have equal true counts, but differ as words and have true-false counts one and zero."))),
                DescribeRole.Theorem))));
}
