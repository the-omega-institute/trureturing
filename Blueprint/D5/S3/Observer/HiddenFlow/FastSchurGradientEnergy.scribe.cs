using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.HiddenFlow;

internal sealed class FastSchurGradientEnergyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual coupled gradient flow has exact dissipation and uniform energy bounds.",
        H("Fast Hidden Gradient Energy"),
        Blocks(
            Paragraph(Text("For positive dimensions p and r, a positive-definite symmetric "
                + "block matrix L, epsilon > 0, and any initial state u0, the trajectory "
                + "is the exponential solution of the full epsilon-scaled block generator. "
                + "The least eigenvalue ell is the exact minimum of the eigenvalues of L. "
                + "All estimates hold for every nonnegative time.")),
            Describe.Lean(
                DescribeId.Create("coupled-exponential-energy-state-velocity"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/HiddenFlow/FastSchurGradientEnergy.coupled_energy_state_velocity"),
                H("Energy, state, and visible velocity of the coupled flow"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The theorem gives the actual initial value and "
                    + "both coordinate ODEs, the exact visible and hidden squared-force "
                    + "dissipation identity, energy antitonicity, the ell-coercive state "
                    + "radius, and the visible derivative bound using the Euclidean "
                    + "operator norm of [A B]. It does not establish the fast residual "
                    + "estimate or the uniform slow-trajectory error of Theorem 20.4."))),
                DescribeRole.Theorem))));
}
