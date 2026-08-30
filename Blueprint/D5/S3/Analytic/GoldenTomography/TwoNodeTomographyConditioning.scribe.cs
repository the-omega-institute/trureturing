using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GoldenTomography;

internal sealed class TwoNodeTomographyConditioningDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/GoldenTomography/TwoNodeTomographyConditioning.";

    public DocumentDefinition Create() => DocumentDefinition.Create(
        ScribeNode.Create(
            "Two-node moment tomography separates exact recovery from metric conditioning.",
            H("Two-Node Tomography Conditioning"),
            Blocks(
                Theorem(
                    "two-distinct-nodes-recover-both-amplitudes",
                    "recover_two_node_amplitudes",
                    "Two Distinct Nodes Recover Both Amplitudes",
                    "The zeroth and first moments determine both hidden amplitudes through explicit division by the node gap."),
                Theorem(
                    "first-amplitude-error-has-an-exact-gap-formula",
                    "recover_first_error",
                    "First-Amplitude Error Has an Exact Gap Formula",
                    "Perturbing both moments changes the recovered first amplitude by an explicit numerator divided by the node separation."),
                Theorem(
                    "second-amplitude-error-has-an-exact-gap-formula",
                    "recover_second_error",
                    "Second-Amplitude Error Has an Exact Gap Formula",
                    "The second recovered amplitude has the complementary exact perturbation formula."),
                Theorem(
                    "first-amplitude-error-is-controlled-by-inverse-separation",
                    "norm_recover_first_error_le",
                    "First-Amplitude Error Is Controlled by Inverse Separation",
                    "The reconstruction error is bounded by the moment perturbation size divided by the norm of the node gap."))));

    private static DocumentBlock.Describe Theorem(
        string id,
        string declaration,
        string title,
        string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromLean(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(paragraph)),
                Paragraph(Text(
                    "Distinct nodes remove the exact kernel. A small node gap can still amplify "
                        + "finite observational error."))),
            DescribeRole.Theorem);
}
