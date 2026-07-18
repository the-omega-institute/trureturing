using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class QubitWitnessesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Schwinger =
        LibraryNoteRef.Create("D5/L/schwinger1960unitary");
    private static readonly LibraryNoteRef Zurek =
        LibraryNoteRef.Create("D5/L/zurek2003decoherence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Quantum/QubitWitnesses",
            "Explicit qubit incompatibility, entanglement, and dephasing witnesses."),
        H("Qubit Witness Skeletons"),
        Blocks(
            new DocumentBlock.Describe(
                DescribeId.Create("pauli-x-and-z-have-no-nonzero-common-eigenvector"),
                DescribeKind.Theorem,
                H("Pauli X and Z have no nonzero common eigenvector"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Quantum/QubitWitnesses.pauli_observables_have_no_common_eigenvector")),
                DescribeProvenance.LiteratureAttested(Schwinger),
                Blocks(Paragraph(Text(
                    "The standard Pauli X and Z observables have no nonzero common eigenvector on C^2. This is an explicit incompatibility witness only: it does not prove the Robertson variance inequality, arbitrary-window full-matrix generation, prime-power tensor factorization, general qudit Weyl relations, or any classical ontology forcing the structure. Original numerical-certificate claim not formalized: the source atom's full matrix-unit relations with exact zero certificate error.")))),
            new DocumentBlock.Describe(
                DescribeId.Create("the-bell-coefficient-matrix-is-not-a-simple-tensor"),
                DescribeKind.Theorem,
                H("The Bell coefficient matrix is not a simple tensor"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Quantum/QubitWitnesses.bell_coefficients_are_not_product")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The coefficient matrix of the unnormalized Bell vector |00> + |11> cannot be factored as an outer product. A nonzero normalization scalar does not change this obstruction. This elementary algebraic witness is proved directly in the repository; Bell's 1964 paper treats the spin singlet and locality, not this exact vector or factorization argument. This declaration proves neither a CHSH expectation nor Tsirelson optimality, a local-hidden-variable bound, Kochen-Specker contextuality, hidden-address interpretations, or that probability is not ignorance. Original numerical-certificate claims not formalized: the source atom's CHSH values 2*sqrt(2) = 2.8284 and the classical local-fiber bound 2.0.")))),
            new DocumentBlock.Describe(
                DescribeId.Create("iterated-phase-damping-has-the-exact-qubit-certificate"),
                DescribeKind.Theorem,
                H("Iterated phase damping has the exact qubit certificate"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Quantum/QubitWitnesses.equal_superposition_phase_damping_certificate")),
                DescribeProvenance.LiteratureAttested(Zurek),
                Blocks(Paragraph(Text(
                    "For the standard real phase-damping map with retention coefficient c in [0,1], N repetitions leave both equal-superposition populations at one half and multiply both coherence entries by c^N. The map is assumed, not derived from a system-environment Hamiltonian. The declaration does not identify this repository's ledger with an environment, bookkeeping with decoherence, or address selection with einselection. Original certificate coverage: the source atom's symbolic (1/2) * c0^N coherence law and fixed one-half populations are formalized exactly; the atom supplies no fixed numeric c0 or N.")))))));
}
