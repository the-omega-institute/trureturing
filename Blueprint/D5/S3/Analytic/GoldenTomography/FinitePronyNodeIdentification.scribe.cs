using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GoldenTomography;

internal sealed class FinitePronyNodeIdentificationDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A full finite recurrence window identifies every separated Prony node carrying nonzero weight.",
        H("Finite Prony Node Identification"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-prony-node-identification"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/GoldenTomography/FinitePronyNodeIdentification."
                        + "finite_prony_node_identification"),
                H("A finite recurrence window identifies the true spectral roots"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For an m-mode exponential moment sequence with pairwise distinct nodes "
                            + "and nonzero weights, any candidate polynomial whose coefficient "
                            + "recurrence vanishes on the first m shifts must evaluate to zero "
                            + "at every true node. The theorem also records that the genuine "
                            + "node-annihilator recurrence supplies a satisfiable witness.")),
                    Paragraph(Text(
                        "The proof converts candidate evaluations into residual mode weights. "
                            + "The recurrence says that the first matching moment window of "
                            + "those residual weights is zero, and finite Vandermonde "
                            + "injectivity forces every residual weight to vanish. Nonzero "
                            + "original weights then expose each candidate root.")),
                    Paragraph(Text(
                        "This is the exact converse layer needed before algorithmic unknown-node "
                            + "Prony recovery. It does not yet select recurrence coefficients, "
                            + "prove uniqueness among monic degree-m candidates, or control root "
                            + "perturbations under noise."))),
                DescribeRole.Theorem)),
        []));
}
