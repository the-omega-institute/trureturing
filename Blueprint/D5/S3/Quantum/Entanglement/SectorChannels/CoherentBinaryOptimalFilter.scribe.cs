using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.SectorChannels;

internal sealed class CoherentBinaryOptimalFilterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact equality in the smaller-Schmidt filter score singles out the largest diagonal-optimal filter.",
        H("Optimal filters for a coherent binary replacement target"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("largest-optimal-filter"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/SectorChannels/CoherentBinaryOptimalFilter.largest_optimal_filter"),
                H("The largest diagonal-optimal filter and its tie"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix the smaller resource mass q and a smaller positive target weight w. For the matched-diagonal score in the symmetric rank-one filter family there are two clipping thresholds, defined algebraically by w=q(2t1-t1 squared)=q t2 squared. The proof maximizes the literal clipped score, identifies every equality case, and selects the largest such filter. Below the transition 2w=q only t1 is optimal, above it only t2 is optimal, and at the transition both optimize.")),
                    Paragraph(Text("The proof uses strict monotonicity outside the two thresholds and an explicit strict chord gap for the intervening convex quadratic. It adds the equality classification and largest-attainer law, not another statement of the previously formalized optimum value.")),
                    Paragraph(Text("Paper motivation, not a Lean conclusion: in the fixed pure Schmidt state model with no communication or shared seed, a common filter retains matched coherence of magnitude at most ab times its strength. The paper argument also classifies optimizing CPTP pairs and equality in trace-norm pinching; those steps and the full coherent quantum-channel plateau are not asserted by this scalar theorem."))),
                DescribeRole.Theorem))));
}
