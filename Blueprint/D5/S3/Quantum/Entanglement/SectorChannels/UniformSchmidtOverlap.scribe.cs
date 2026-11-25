using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.SectorChannels;

internal sealed class UniformSchmidtOverlapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compare arbitrary coherent finite local columns with an explicit private-randomness protocol for uniform matching labels.",
        H("Uniform matched-label overlap for every Schmidt spectrum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("uniform-schmidt-matched-overlap"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/SectorChannels/UniformSchmidtOverlap.uniform_matched_overlap"),
                H("Coherent upper bound and constructive lower bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For m positive output labels and Schmidt probabilities p, set Z to the sum over atoms of min(p, sqrt(p/m)). The matched overlap caps each actual matching Born probability at 1/m and sums the caps.")),
                    Paragraph(Text("For arbitrary local isometric Kraus columns, the light substate has a squared-norm budget and the heavy substate an amplitude-sum budget. Applying the cap to the amplitude triangle and completing the square gives overlap at most 4Z/3 without a rank restriction.")),
                    Paragraph(Text("The constructed local columns give exactly the measured output law of a common Schmidt-basis measurement followed by independent stochastic draws on each side. Adjacent integer heavy block sizes and a least-load assignment on the remaining labels give overlap at least Z/sqrt(2).")),
                    Paragraph(Text("This is a finite Born-overlap theorem on the fixed pure Schmidt resource, not the full input-dependent channel problem or a diamond-distance formalization."))),
                DescribeRole.Theorem))));
}
