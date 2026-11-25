using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Decoherence;

internal sealed class FourLevelBathPhysicalDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Decoherence/FourLevelBathPhysical.";
    private static readonly LibraryNoteRef ThermalOperations =
        LibraryNoteRef.Create("D5/L/Resource/vomende2022thermaloperations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed nondegenerate Gibbs bath realizes qutrit pinching exactly when its weighted phase columns are orthonormal.",
        H("Pinching by a fixed four-level Gibbs bath"),
        Blocks(
            Paragraph(Text(
                "The qutrit has zero Hamiltonian. Fix four distinct bath energies E and a finite real inverse "
                + "temperature β, and let p be the resulting Gibbs law. The joint Hamiltonian is I ⊗ diag(E). "
                + "The input is the qutrit state tensored with diag(p), and the reduced channel traces out "
                + "the bath after an exactly energy-conserving unitary. This is the finite-bath model of "
                + "vom Ende, Eq. (1) in Section II.")),
            Theorem("fixed-bath-pinching", "fixed_bath_pinching_iff", "Fixed-bath phase criterion",
                "For these same E and β, one unitary pinches every qutrit density state exactly if there "
                + "are unit phases z(b,i) for which W[b,i] = √p(b) z(b,i) and WᴴW = I₃. Distinct energies "
                + "give one qutrit block per bath level. Fixing the basis projectors and strict positivity "
                + "of p force each block to be diagonal. A coherent density with every entry 1/3 then "
                + "determines the off-diagonal Gram entries. In the reduced matrix map, the multiplier "
                + "of Xᵢⱼ is (WᴴW)ⱼᵢ."),
            Theorem("phase-pinching-on-matrices", "phase_implements_pinching", "Pinching on all matrices",
                "The diagonal phase construction gives coordinate pinching on every complex qutrit "
                + "matrix under the weighted Gram condition."),
            Theorem("bath-return", "bath_return", "The bath marginal returns",
                "For any energy-conserving unitary at the fixed injective energy list, any real "
                + "diagonal bath matrix and any trace-one input matrix, the outgoing bath marginal equals "
                + "the initial diagonal bath matrix. The joint output can carry correlations."),
            Theorem("zero-endpoint-bath-heat", "zero_heat", "Zero endpoint bath heat",
                "For each density input, the final minus initial bath mean energy is zero. The system "
                + "Hamiltonian is zero at both endpoints. This energy statement concerns the specified interaction."),
            Theorem("phase-realization", "phase_realization", "One unitary realizes the phase witness",
                "Unit phases with identity Gram give a unitary commuting with the total Hamiltonian, "
                + "pinching on the matrix algebra, and bath return and zero bath heat on density inputs."),
            Theorem("matching-distinct-energies", "matching_distinct_energies", "Matching a prescribed law",
                "If the bath energies may be chosen, at each β > 0 a positive, normalized, pairwise "
                + "distinct law p is realized by the injective list E(b) = −log(p(b))/β."))));

    private static DocumentBlock.Describe Theorem(string id, string name, string title, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(ThermalOperations),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);
}
