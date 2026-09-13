using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class DampedObservationRevivalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fading state amplitude and disappearance of its observation are different mathematical events.",
        H("Damped Modes and an Initially Invisible Readout"),
        Blocks(
            Paragraph(Text(
                "After one initial excitation (1,-1), the autonomous map multiplies "
                + "the first coordinate by a and the second by b, with 0<b<a<1. "
                + "There is no later input. The observation is the sum of the two "
                + "coordinates and may therefore cancel.")),
            Describe.Lean(
                DescribeId.Create("strict-decay-with-visible-revival"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/DampedObservationRevival.decay_and_visibility_are_distinct"),
                H("A strictly fading state can become visible after a zero observation"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Induction derives the actual trajectory (a^n,-b^n). Its squared "
                        + "Euclidean amplitude strictly decreases at every step, while the "
                        + "readout is zero initially and positive at every later time. "
                        + "The theorem also gives the exact first difference of a^n-b^n "
                        + "and proves that the readout tends to zero.")),
                    Paragraph(Text(
                        "This is a linear dynamical model of the distinction between "
                        + "attenuation and visibility, not a theorem about the human mind. "
                        + "Hobbes's discussion in Leviathan, chapters II-III, supplies "
                        + "historical motivation only. Signed amplitudes are not probabilities; "
                        + "squared amplitude is not asserted to be physiological energy. "
                        + "External sensory competition would require an additional model."))),
                DescribeRole.Theorem))));
}
