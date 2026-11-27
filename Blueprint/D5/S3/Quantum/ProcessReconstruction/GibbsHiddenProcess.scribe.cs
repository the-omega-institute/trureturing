using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.ProcessReconstruction;

internal sealed class GibbsHiddenProcessDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/ProcessReconstruction/GibbsHiddenProcess";

    private static readonly LibraryNoteRef CarlenMaas =
        LibraryNoteRef.Create("D5/L/ProcessReconstruction/carlen2017gradient");

    private static readonly LibraryNoteRef WalckLyons =
        LibraryNoteRef.Create("D5/L/ProcessReconstruction/walck2008ghz");

    private static readonly LibraryNoteRef Haapasalo =
        LibraryNoteRef.Create("D5/L/ProcessReconstruction/haapasalo2012extremal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two primitive GNS-symmetric semigroups at the same faithful Gibbs equilibrium "
        + "have identical proper output channels at every time.",
        H("Hidden Process Coherence at Gibbs Equilibrium"),
        Blocks(
            Paragraph(Text(
                "This is an extra-dynamics example alongside static process reconstruction. "
                + "Fix at least two qubits, a Hamiltonian diagonal in the computational basis, "
                + "a common inverse temperature β > 0, and a common reset rate γ > 0. "
                + "Construct the two time-homogeneous semigroups using the rank-two Schur "
                + "channels and reset to the same Gibbs density. These are explicit choices "
                + "for the construction. The model specifies finite-system channels. "
                + "A geometrically local physical bath, finite reservoir, or energy-preserving "
                + "dilation requires additional hypotheses.")),
            Describe.Lean(DescribeId.Create("faithful-gibbs-equilibrium"),
                DeclarationHandle.Create(Module + ".gibbs_register_dynamics"),
                H("Common faithful equilibrium and primitivity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(CarlenMaas),
                Blocks(
                    Paragraph(Text(
                        "For H = diag(E), the equilibrium τ is the normalized diagonal matrix "
                        + "of Boltzmann weights exp(−β Eₓ). All weights are positive, including "
                        + "for degenerate H. The semigroup laws, stationarity of τ and finite-time "
                        + "Heisenberg GNS symmetry hold for both choices of the Schur channel. "
                        + "Each flow also commutes with the conjugations of the same H by "
                        + "the diagonal Hamiltonian covariance result.")),
                    Paragraph(Text(
                        "For every t > 0 the reset has positive weight. On any nonzero positive "
                        + "input X it contributes a positive multiple of the faithful τ, so Γₜ(X) "
                        + "is positive definite. The reset weight tends to one, and the other "
                        + "component tends to zero on every input because the dephasing "
                        + "multipliers have absolute value at most one. The limit is "
                        + "X ↦ tr(X)τ, which gives uniqueness of the stationary density. "
                        + "The detailed balance convention is Carlen and Maas, "
                        + "arXiv:1609.01254v3, p. 8, Definition 2.10."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("proper-output-ambiguity"),
                DeclarationHandle.Create(Module + ".gibbs_hidden_process"),
                H("Identical proper outputs and exact diamond separation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(WalckLyons, Haapasalo),
                Blocks(
                    Paragraph(Text(
                        "Let u and v be the all-zero and all-one words. The common reset cancels "
                        + "when taking the channel difference. Only the two ordered coherences "
                        + "(u,v) and (v,u) differ, with dephasing multipliers 1 and exp(−2t). "
                        + "The difference is therefore exp(−γt)(1 − exp(−2t))/2 times the "
                        + "static rank-two channel difference. Tracing out any qubit kills "
                        + "both coherences. Equality holds as maps on the entire input algebra "
                        + "at every t ≥ 0, so it also holds after any finite reference extension.")),
                    Paragraph(Text(
                        "The unhalved global diamond distance is exp(−γt)(1 − exp(−2t)), "
                        + "by the exact static value two and nonnegative scaling on amplified "
                        + "inputs. The balanced GHZ input attains the bound. The value is "
                        + "strictly positive for every t > 0.")),
                    Paragraph(Text(
                        "Walck and Lyons, arXiv:0707.4428v2, p. 2, Main Result and the first "
                        + "direction of its proof, exhibit the same coherence loss for states. "
                        + "Haapasalo, Heinosaari and Pellonpää, arXiv:1209.5933v1, p. 8, "
                        + "Section 4, Definition 3 and Eqs. (12)–(13), formulate channel "
                        + "marginals directly. The equality and diamond formula above are for "
                        + "the two constructed semigroups."))),
                DescribeRole.Theorem))));
}
