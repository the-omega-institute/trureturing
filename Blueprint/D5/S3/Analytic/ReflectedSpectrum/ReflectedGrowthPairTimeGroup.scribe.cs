using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ReflectedSpectrum;

internal sealed class ReflectedGrowthPairTimeGroupDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/ReflectedSpectrum/ReflectedGrowthPairTimeGroup.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The oriented reflected pair is a faithful multiplicative flow, while symmetric observation identifies opposite parameter directions.",
        H("Reflected Growth Pair Time Group"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("oriented-even-odd-observation"),
                DeclarationHandle.Create(Prefix + "orientedEvenOddObservation"),
                H("Joint even-odd observation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The joint observer records both the reflection-invariant even channel and the oriented odd channel already defined by the frozen even-odd decomposition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reflected-time-group"),
                DeclarationHandle.Create(Prefix + "reflected_growth_pair_time_group"),
                H("The reflected pair is a one-parameter multiplicative group"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The value at zero is the multiplicative identity, parameter addition becomes coordinatewise multiplication, and parameter reversal gives the inverse pair."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("oriented-pair-injective"),
                DeclarationHandle.Create(Prefix + "reflected_growth_pair_injective"),
                H("A nonzero split makes the oriented pair faithful"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Real exponential injectivity and the nonzero split recover the parameter from the first branch of the full pair."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("symmetric-observer-loss"),
                DeclarationHandle.Create(Prefix + "reflected_growth_sum_not_injective"),
                H("Symmetric observation loses parameter orientation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The frozen evenness theorem supplies the explicit collision between parameter values one and minus one, so the branch-forgetting readout is never injective."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("joint-observer-recovery"),
                DeclarationHandle.Create(Prefix + "oriented_even_odd_observation_injective"),
                H("Even and odd channels together restore orientation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Exact branch reconstruction converts equality of joint observations into equality of the positive-rate exponential branch, which recovers the parameter for a nonzero split."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("time-recovery-package"),
                DeclarationHandle.Create(Prefix +
                    "oriented_time_recovery_symmetric_time_loss"),
                H("Oriented time recovery and symmetric time loss"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The packaged theorem separates three facts: the full pair is faithful, the symmetric quotient loses orientation, and adjoining the odd channel restores faithful observation. Negative parameter is represented by the inverse group element."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/ReflectedSpectrum/ReflectedGrowthPairEvenOddDecomposition")),
        ]));
}
