using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSUniformHardCoreEnergyDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreEnergy";
    private static LibraryNoteRef Lesanovsky =>
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/lesanovsky2012constrainedspinchain");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The compressed periodic hard-core Dirichlet form",
        H("Shifted energy on cyclic independent configurations"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodic-hard-core-shifted-laplacians"),
                DeclarationHandle.Create(Module + ".shiftedHamiltonian_eq_laplacians"),
                H("Flip and hop Laplacians"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Lesanovsky),
                Blocks(
                    Paragraph(Text("For n ≥ 7, the diagonal n − |S| equals the weighted degree of the moves out of each independent configuration S. The shifted matrix is the flip-graph Laplacian plus one half of the hop-graph Laplacian.")),
                    Paragraph(Text("Lesanovsky's constrained parent has the same equal-weight periodic ground state at z = 1. The operator here includes a half-weight nearest-neighbor hop, which supplies the row balance for the adjacent-marginal argument."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodic-hard-core-dirichlet-form"),
                DeclarationHandle.Create(Module + ".shiftedEnergy_eq_dirichlet"),
                H("Dirichlet form for complex amplitudes"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The shifted energy is half the sum over ordered pairs of independent configurations of the transition weight times the squared modulus of their amplitude difference. The weights are one on flips and one half on hops. Splitting the amplitudes into real and imaginary parts gives the complex identity and shows nonnegativity."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodic-hard-core-zero-energy-rigidity"),
                DeclarationHandle.Create(Module + ".shiftedEnergy_eq_zero_iff"),
                H("Zero energy forces equal amplitudes"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For n ≥ 7, the shifted energy is zero exactly when every amplitude equals the amplitude at the empty configuration. Each summand is nonnegative, so zero energy forces equality across each edge of positive weight. The deletion path from any independent configuration to the empty one uses only weight-one flips. Constant amplitudes make every squared difference zero."))),
                DescribeRole.Theorem))));
}
