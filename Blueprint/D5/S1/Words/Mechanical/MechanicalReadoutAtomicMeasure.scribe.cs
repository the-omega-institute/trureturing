using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical;

internal sealed class MechanicalReadoutAtomicMeasureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Mechanical/MechanicalReadoutAtomicMeasure.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The completed mechanical readout is the distribution function of a numbered atomic probability measure.",
        H("Mechanical Readout Atomic Measure"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mechanical-atomic-probability-carrier"),
                DeclarationHandle.Create(Prefix + "geometric_atomic_probability_and_carrier"),
                H("Probability and concentration"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For 0 <= r < 1 and each positive time k, retain all k threshold locations (j-x)/k with their common weight (1-r)^2 r^(k-1). The index records both k and j, so equal locations reached at different times retain separate mass. The geometric mass identity makes the resulting countable Dirac sum a probability measure. Every listed location lies in (0,1] when the phase is in [0,1), and the measure assigns that interval mass one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mechanical-atomic-distribution-function"),
                DeclarationHandle.Create(Prefix + "geometric_atomic_apply_Iic"),
                H("Distribution function"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On slopes in [0,1], evaluating the atomic measure on the half-line up to the slope gives the completed geometric readout. At each time, the counted atoms are exactly the thresholds crossed by the cumulative floor; summing these finite counts and then all times gives the distribution function."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mechanical-atomic-integer-hits"),
                DeclarationHandle.Create(Prefix + "geometric_atomic_singleton_hit"),
                H("Mass of an interior threshold"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At an interior slope, a time k contributes one threshold atom precisely when x+k times the slope is an integer. There is at most one such threshold at each fixed time, while hits at different times all contribute. The singleton mass is the sum of their geometric weights. The interior condition excludes the zero-slope endpoint, where an integer hit can correspond to the omitted index j=0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mechanical-atomic-left-jump"),
                DeclarationHandle.Create(Prefix + "geometric_readout_left_jump_exact"),
                H("Exact left jump"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("As a slope approaches an interior value from below, the measures of its closed threshold half-lines converge to the measure of the open half-line at that value. The completed readout therefore has a real left limit equal to that open-half-line mass. Its value at the slope exceeds the limit by exactly the singleton mass, hence by the real sum of the weights at every integer-hit time. Coincident hits are retained."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mechanical-atomic-rational-jump"),
                DeclarationHandle.Create(Prefix + "geometric_rational_left_jump_closed_form"),
                H("Reduced rational jump"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At zero phase and a reduced interior slope p/q, positive integer hits occur exactly at multiples of q. Splitting the actual hit-weight series after its first q terms gives a q-step tail recurrence. Its first block contains only the weight at time q, and solving the recurrence yields the left jump (1-r)^2 r^(q-1)/(1-r^q). The left limit is the real limit supplied by the atomic distribution function."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mechanical-atomic-closed-support"),
                DeclarationHandle.Create(Prefix + "geometric_atomic_support"),
                H("Closed support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When the ratio is strictly between zero and one, every numbered threshold has positive mass. At level k, the threshold with index floor(ky)+1 approaches any y in [0,1) as k grows. Closedness adds the upper endpoint, while concentration on (0,1] excludes every point outside [0,1]. Thus the topological support is the full closed unit interval, although the measure is atomic."))),
                DescribeRole.Theorem))));
}
