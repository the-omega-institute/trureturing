using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical;

internal sealed class MechanicalReadoutUniformLimitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Mechanical/MechanicalReadoutUniformLimit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Geometric mechanical readouts approach their slope uniformly as the weights flatten.",
        H("Mechanical Readout Uniform Limit"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mechanical-geometric-readout-uniform-limit"),
                DeclarationHandle.Create(Prefix + "geometric_readout_uniform_slope_bound"),
                H("One-sided slope approximation and a joint error budget"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every slope in [0,1), every real phase, and every geometric ratio in [0,1), the completed readout differs from the slope by an amount between (1-r)*(fract(x)-1) and (1-r)*fract(x). The cumulative floor discrepancy is exactly fract(x)-fract(x+k*alpha). Finite Abel summation combines the terminal coefficient with the nonnegative successive weight drops; together they have total 1-r, and the geometric tail passes the one-sided bounds to the infinite readout. In particular, its absolute error is at most 1-r. For any target slope and finite horizon n, the truncated readout differs from the target by at most r^n plus 1-r plus the parameter distance. These estimates hold uniformly in phase, including phases where the fixed-ratio readout jumps as a function of slope. The same completion bound and the existing geometric tail also determine the two orders of limits. For a slope alpha in [0,1) and a phase x in [0,1), write P_{r,n} for weightedPrefix with weights (1-r)*r^j and G_r for geometricReadout. For each fixed r in (0,1), the tail 0 <= G_r-P_{r,n} <= r^n tends to zero as n tends to infinity. Next, the uniform bound |G_r-alpha| <= 1-r sends the completed value to alpha as r approaches one from below. In the reverse order, each fixed finite n has only finitely many terms, and every weight (1-r)*r^j tends to zero as r approaches one from below; hence the inner limit is zero. Its subsequent limit as n tends to infinity is still zero. The two iterated limits are therefore alpha and zero, and they differ whenever alpha > 0. These are consequences of the existing completion and uniform-bound results and continuity of finite sums. This averaging changes the weights themselves; it does not assert that the fixed binary ratio r = 1/2 approaches alpha or is uniformly continuous in slope."))),
                DescribeRole.Theorem))));
}
