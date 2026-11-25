using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class PetzFixedMarginalNoiseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Environmental replacement preserves both retained marginals, contracts the supported relative entropy loss, and preserves strict ordinary Petz scores at small positive noise.",
        H("Fixed-marginal noise for ordinary Petz recovery"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("noise-loss-contraction"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/PetzFixedMarginalNoise.noise_loss_contract"),
                H("Contraction of the supported entropy loss"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For each input, mix its joint state with the product of its own retained marginal and the normalized identity on the environment. The source is supported inside the reference, and the retained reference marginal is faithful. The entropy loss is the full trace-log relative entropy minus the trace-log relative entropy of the retained pair.")),
                    Paragraph(Text("The replacement pair has exactly the retained entropy. Its uniform environment makes the trace-log expression a sum of identical scaled blocks. Joint convexity bounds the noisy entropy by the two weighted entropies, and the retained term is fixed for each input. The resulting loss is nonnegative and bounded above by the original loss times one minus the noise weight, including both endpoints."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("strict-ordinary-petz-score"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/PetzFixedMarginalNoise.exists_strict_score_noise"),
                H("Persistence of a strict ordinary Petz score"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The score divides the unhalved squared trace norm of the ordinary Petz reconstruction error by the supported entropy loss. At any positive original loss and any real threshold strictly below the score, a weight strictly between zero and one preserves the strict inequality. Both original marginals are fixed. The noisy joint reference is faithful and contains the support of the noisy source. The noisy source is faithful whenever its retained marginal is faithful. The noisy loss is positive and satisfies the contraction above.")),
                    Paragraph(Text("Fixing the marginals fixes the middle factor of the Petz map. Continuity of the square root on the joint reference and continuity of the supported entropy along the mixture give right continuity of the score at zero. The replacement term gives the noisy reference a strictly positive spectral floor."))),
                DescribeRole.Theorem))));
}
