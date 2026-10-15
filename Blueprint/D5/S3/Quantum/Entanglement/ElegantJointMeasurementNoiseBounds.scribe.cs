using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class ElegantJointMeasurementNoiseBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform marginals and L1 control for the physical independently noisy EJM triangle.",
        H("Physical EJM Noise Bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("physical-ejm-noise-l1-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/ElegantJointMeasurementNoiseBounds.ejm_noise_l1_bound"),
                H("Three independent source deficits bound the full observed law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The visibilities x, y and z belong to [0,1] and refer to the AB, BC and CA singlet sources in the actual six-qubit EJM Born law. The L1 distance sums the absolute probability differences over all 64 ordered outcomes.")),
                    Paragraph(Text("The exact eight-term independent-source mixture contains the ideal three-singlet endpoint with weight xyz. All its other terms are nonnegative. Thus the noisy law dominates xyz times the ideal law, and normalization bounds the L1 distance by 2(1-xyz), hence by twice the sum of the three visibility deficits.")),
                    Paragraph(Text("The A and B one-party marginals remain exactly 1/4 for every real triple of visibilities as polynomial identities. These are the singletons used by the original inflation score. The L1 result is a physical noise bound, and by itself asserts neither positivity of an inflation certificate nor nonlocality."))),
                DescribeRole.Theorem))));
}
