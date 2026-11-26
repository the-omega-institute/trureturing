using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PureState;

internal sealed class FourierMemoryEncoderDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/PureState/FourierMemoryEncoder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite translate mixture gives a common CPTP encoder for Fourier character records.",
        H("Encoding into a subset of a finite abelian carrier"),
        Blocks(
            Describe.Lean(DescribeId.Create("fourier-memory-restricted-povm"),
                DeclarationHandle.Create(Module + "sum_characterEffect"),
                H("Restricted characters resolve the memory identity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Take a finite abelian group G of order N and a nonempty subset A as the output basis. Each effect is the rank-one matrix of the corresponding restricted character, scaled by 1/N. Orthogonality of the character sums makes the effects sum to the identity on A."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourier-memory-translate-encoder"),
                DeclarationHandle.Create(Module + "character_encoder_attains"),
                H("The translate encoder attains the prescribed profile score"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Suppose dᵢ is the probability that i lies in A + z when z is drawn with weights b(z). The branch indexed by z sends coordinate a + z to a with coefficient √b(z)/√dₐ₊ᶻ on the positive support of d. The sum of the branch Grams is the projection onto that support. Completing the channel resets the complementary coordinates to a fixed basis state in A. The signal has zero amplitude on that complement.")),
                    Paragraph(Text("Use tᵢ = √dᵢ rᵢ with rᵢ = c wherever dᵢ < 1. Every coordinate with dᵢ = 1 lies in each translate of positive weight, so the sum of the rᵢ on any such translate is the profile value. The Fourier phase of a translation is a single unit-modulus factor for each character. Thus after summing branches the restricted POVM gives the same score, the squared profile value divided by N, for each label. The historical novelty of this common encoder remains provisional."))),
                DescribeRole.Theorem))));
}
