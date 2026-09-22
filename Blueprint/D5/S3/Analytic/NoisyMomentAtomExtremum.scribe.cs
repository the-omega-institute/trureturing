using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class NoisyMomentAtomExtremumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/NoisyMomentAtomExtremum.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positivity-preserving perturbation of Lagrange weights attains the exact finite noisy exterior-atom optimum.",
        H("Noisy Moment Atom Extremum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("noisy-moment-atom-extremum-feasible-set"),
                DeclarationHandle.Create(Prefix + "momentAtomSet"),
                H("Actual feasible probability weights"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two nonnegative normalized weight vectors, one with an additional atom at y, have coordinatewise-close raw moments through degree card(iota)-1. Zeroth-moment equality follows from the two exact normalizations."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("noisy-moment-atom-extremum-exact-small-noise-optimum"),
                DeclarationHandle.Create(Prefix + "finite_noisy_exterior_atom_sharp"),
                H("Constructive attained optimum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary distinct real nodes and an off-node point y, form Lagrange extrapolation coefficients c, their positive-sign 0/1 interpolant p, P=p(y), and the nonconstant coefficient cost L. A computed positive noise radius preserves the signs of c after a worst-direction moment perturbation. The proof constructs both probability vectors, verifies their normalization and saturated moment errors, and proves that the maximum atom at y equals (1+epsilon L)/P. The IsGreatest upper bound ranges over all feasible probability pairs on the specified supports."))),
                DescribeRole.Theorem))));
}
