using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.ProcessReconstruction;

internal sealed class HiddenProcessSemigroupDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/ProcessReconstruction/HiddenProcessSemigroup";

    private static readonly LibraryNoteRef CarlenMaas =
        LibraryNoteRef.Create("D5/L/ProcessReconstruction/carlen2017gradient");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit finite reset semigroups from the rank-two Schur channels.",
        H("Reset Semigroups from Rank-Two Channels"),
        Blocks(
            Describe.Lean(DescribeId.Create("time-composition"),
                DeclarationHandle.Create(Module + ".flow_add"),
                H("Finite channel construction and time composition"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Φ be either static rank-two channel and Rτ(X) = tr(X)τ for a "
                        + "diagonal density τ. Write Φ as the average of conjugations by the two "
                        + "commuting diagonal involutions of the static construction. For t ≥ 0 "
                        + "mix each conjugation with the identity using identity weight "
                        + "p = (1 + exp(−t))/2 and compose the two mixtures. This gives a CPTP "
                        + "channel Tₜ, with matrix-unit multipliers exp(t(cₓᵧ − 1)), "
                        + "where cₓᵧ is the multiplier of Φ.")),
                    Paragraph(Text(
                        "With a common rate γ, the finite-time channel is Γₜ = exp(−γt) Tₜ "
                        + "+ (1 − exp(−γt)) Rτ. The Schur multipliers multiply under time "
                        + "addition. The dephasing channels preserve trace and fix τ, so "
                        + "TₜRτ = RτTₜ = Rτ, and Rτ² = Rτ. These identities give "
                        + "ΓₛΓₜ = Γₛ₊ₜ, with Γ₀ the identity."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("norm-continuity"),
                DeclarationHandle.Create(Module + ".flow_norm_continuous"),
                H("Continuity in channel operator norm"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The real exponential coefficients are continuous. Finite "
                    + "dimensionality of the matrix algebra gives continuity in the norm "
                    + "of continuous linear maps."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("schrodinger-generator"),
                DeclarationHandle.Create(Module + ".flow_generator"),
                H("Right derivative at time zero"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Differentiating the two exponential coefficients at zero on each "
                    + "matrix entry yields L = Φ − id + γ(Rτ − id)."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("heisenberg-duality"),
                DeclarationHandle.Create(Module + ".heisenberg_trace_dual"),
                H("Trace dual of the finite-time channel"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The real symmetric Schur multiplier gives the same Schur part in the "
                    + "trace-dual observable map. The dual reset sends A to tr(τA) I, "
                    + "and Γₜ is unital in the Heisenberg picture."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gns-symmetry"),
                DeclarationHandle.Create(Module + ".heisenberg_gns_symmetric"),
                H("GNS detailed balance for the observable semigroup"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(CarlenMaas),
                Blocks(
                    Paragraph(Text(
                        "The matrix units are orthogonal in the pairing tr(τ A†B). "
                        + "The Schur multipliers are real, and the dual reset is the "
                        + "orthogonal projection onto the identity line for faithful τ. "
                        + "This proves symmetry at every time and uses the same pairing "
                        + "as Carlen and Maas, arXiv:1609.01254v3, p. 6, Definition 2.2 "
                        + "and Eq. (2.3) at s = 1, and p. 8, Definition 2.10."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gns-generator"),
                DeclarationHandle.Create(Module + ".heisenberg_generator_gns_symmetric"),
                H("GNS symmetry of the observable generator"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(CarlenMaas),
                Blocks(Paragraph(Text(
                    "The generator uses the real exponential rates as its Schur "
                    + "coefficients and γ as the coefficient of the dual reset. "
                    + "Both terms are symmetric for the same pairing. The observable "
                    + "generator is also the entrywise right derivative at zero."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hamiltonian-covariance"),
                DeclarationHandle.Create(Module + ".flow_commutes_hamiltonian_propagator"),
                H("Covariance under the diagonal Hamiltonian"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(CarlenMaas),
                Blocks(
                    Paragraph(Text(
                        "Conjugation by exp(−isH) for diagonal H multiplies the same "
                        + "matrix units by phases, so it commutes with the Schur component. "
                        + "The reset commutes because conjugation preserves trace and fixes τ. "
                        + "For a Gibbs τ at positive inverse temperature, this is the "
                        + "Hamiltonian covariance associated to its modular group. "
                        + "See Carlen and Maas, arXiv:1609.01254v3, p. 4, Definition 1.1 "
                        + "and Eq. (1.2), and pp. 8–9, Theorem 2.9(1) and Remark 2.11, Eq. (2.8)."))),
                DescribeRole.Theorem))));
}
