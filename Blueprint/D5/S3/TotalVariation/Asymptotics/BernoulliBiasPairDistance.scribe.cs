using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation.Asymptotics;

internal sealed class BernoulliBiasPairDistanceDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/TotalVariation/Asymptotics/BernoulliBiasPairDistance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Any two canonical Bool bias laws have total variation equal to the absolute difference of their bias parameters.",
        H("Bernoulli Bias Pair Distance"),
        Blocks(
            Paragraph(Text(
                "The repository already owns the canonical positiveBiasLaw and the finite "
                    + "total-variation normalization. The symmetric plus-delta versus "
                    + "minus-delta case was already public. Repository search found no "
                    + "generic public identity for two arbitrary bias parameters, so this "
                    + "module adds only that missing algebraic adapter.")),
            Describe.Lean(
                DescribeId.Create("bias-pair-tv"),
                DeclarationHandle.Create(Prefix + "positive_bias_pair_total_variation"),
                H("Exact total variation between arbitrary bias parameters"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every real delta and epsilon, the half-L1 distance between positiveBiasLaw delta and positiveBiasLaw epsilon is abs(delta-epsilon). The identity itself does not require probability-range hypotheses."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("probability-pair-tv"),
                DeclarationHandle.Create(Prefix + "plus_probability_pair_total_variation"),
                H("Plus-port probability gap is total variation"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Writing a Bool law by its true probability p gives bias p-1/2. In these coordinates total variation is exactly abs(p-q)."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Probability semantics remain owned by SymmetricBernoulliProbabilityData. "
                    + "This file does not duplicate normalization or nonnegativity proofs."))))));
}
