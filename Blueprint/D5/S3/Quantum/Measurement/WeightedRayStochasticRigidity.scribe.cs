using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class WeightedRayStochasticRigidityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/WeightedRayStochasticRigidity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A unitary stochastic transport of weighted pure projections permutes their distinct rays and conserves the total weight of each group.",
        H("Weighted pure rays and stochastic transport"),
        Blocks(
            Describe.Lean(DescribeId.Create("weighted-ray-transport"),
                DeclarationHandle.Create(Prefix + "weighted_ray_transport"),
                H("Common ray permutation and grouped weight conservation"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The finite outcome set maps surjectively onto a finite set of distinct rays. Each ray is represented by a Hermitian idempotent matrix of trace one. Every outcome has a strictly positive real weight. A single unitary and a single nonnegative column-stochastic matrix satisfy the displayed effect transport identity for every output row.")),
                    Paragraph(Text("Pair each row identity with the complementary projection of its conjugated output ray. Every summand has nonnegative trace, and the total is zero. Any nonzero coefficient therefore pairs to zero with that complement. Two trace-one projections with this property coincide: the trace of the conjugate-transpose square of their difference vanishes.")),
                    Paragraph(Text("Every row uses an input because its trace is strictly positive. Unitary conjugation is injective, so the induced map of the finite set of distinct rays is a permutation. Its support condition restricts every nonzero stochastic coefficient to the corresponding group. Summing row traces within a group and using the column sums gives equality of the two grouped weights.")),
                    Paragraph(Text("The weights of repeated outcomes are added before comparing groups. No inverse stochastic matrix is assumed. These matrix statements concern a specified Born probability interface; they supply no actual event law, preparation, calibration, or physical access to inputs."))),
                DescribeRole.Theorem))));
}
