using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class NoisyMomentPhaseBoundaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/NoisyMomentPhaseBoundary.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The initial noisy-moment optimum has an exact support-transition boundary and a unique attaining probability pair.",
        H("Noisy Moment Phase Boundary"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("noisy-moment-phase-exact-classification"),
                DeclarationHandle.Create(Prefix + "exact_noise_phase_classification"),
                H("Exact attainment and rigidity at every noise level"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For distinct real nodes and an off-node point, the Lagrange 0/1 dual polynomial determines P, the coefficient cost L, the signed perturbation r, and transition slopes A_i=P*r_i/c_i-L. If every nonconstant dual coefficient is nonzero, a positive normalized probability pair attains (1+epsilon*L)/P exactly when every epsilon*A_i is at most one and its weights equal the computed positive and negative parts. Necessity follows by decomposing the dual gap into nonnegative nodal and coordinate slacks, forcing each noisy moment to saturate and then forcing every nodal weight. Sufficiency constructs the normalized pair and verifies all moments. Equality at the first transition is included. This sharpens a sufficient small-noise radius into an exact boundary; it does not assume a pre-existing optimality or complementary-slackness witness. Later phases and zero dual coefficients are separate questions."))),
                DescribeRole.Theorem))));
}
