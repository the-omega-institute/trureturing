using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GoldenTomography;

internal sealed class FinitePronyHankelReconstructionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Separated finite exponential modes satisfy an annihilating recurrence and have full-rank Hankel sections.",
        H("Finite Prony-Hankel Reconstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-prony-hankel-reconstruction"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/GoldenTomography/FinitePronyHankelReconstruction."
                        + "finite_prony_hankel_reconstruction"),
                H("Separated finite exponential modes have exact Prony recurrence and Hankel rank"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite family of nodes and weights, the theorem packages the "
                            + "node-annihilator recurrence, the Vandermonde-diagonal-"
                            + "Vandermonde-transpose factorization of every Hankel section, "
                            + "injective recovery of weights from the first matching moments "
                            + "when the nodes are distinct, and exact Hankel rank when the "
                            + "section is large enough and every weight is nonzero.")),
                    Paragraph(Text(
                        "The declaration formalizes the exact noiseless finite layer shared by "
                            + "Prony reconstruction, matrix-pencil methods, finite Koopman "
                            + "delay models, and Hankel dynamic mode decomposition. It does not "
                            + "assert numerical conditioning, noisy node recovery, confluent "
                            + "reconstruction, or an infinite-rank operator theorem."))),
                DescribeRole.Theorem)),
        []));
}
