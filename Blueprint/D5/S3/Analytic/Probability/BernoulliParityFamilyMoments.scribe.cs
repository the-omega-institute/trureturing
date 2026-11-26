using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class BernoulliParityFamilyMomentsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint independence of a finite family of affine parities of Bernoulli bits.",
        H("Joint independence of affine Bernoulli parities"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bernoulli-parity-family-independent"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Probability/BernoulliParityFamilyMoments.bernoulli_parity_family_independent_iff"),
                H("Fair-coordinate linear independence and disjoint biased supports"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take finitely many independent Bernoulli bits, each with probability of "
                        + "one strictly positive and at most one half. Each output adds an arbitrary "
                        + "binary offset to a binary linear combination of the bits. Joint mass "
                        + "factors into marginal masses at every output vector if and only if "
                        + "two conditions hold. The nonzero restrictions of the indexed rows to "
                        + "fair bits are linearly independent over the field with two elements. "
                        + "Any two distinct rows whose fair restrictions vanish have disjoint "
                        + "supports. Constant outputs are allowed.")),
                    Paragraph(Text(
                        "Mixed sign moments determine the finite Boolean law. The moment for a "
                        + "subset of outputs is the offset sign times the product of the biases "
                        + "on the support of the binary row sum. A moment vanishes exactly when "
                        + "that sum meets a fair coordinate. For two biased-only rows, overlap "
                        + "cancels a shared coordinate in the sum and strictly increases the "
                        + "moment of the linear part above the product of the two moments. "
                        + "The offset signs appear on both sides of moment factorization."))),
                DescribeRole.Theorem))));
}
