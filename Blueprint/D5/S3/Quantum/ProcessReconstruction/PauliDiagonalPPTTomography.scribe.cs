using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.ProcessReconstruction;

internal sealed class PauliDiagonalPPTTomographyDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/ProcessReconstruction/PauliDiagonalPPTTomography.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ProcessReconstruction/singh2026boundtomography");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp worst-direction conditioning for process tomography with four-dimensional Pauli-diagonal PPT probes.",
        H("Pauli-diagonal PPT probes for process tomography"),
        Blocks(
            Theorem("ppt-process-pauli-upper", "two_qubit_diagonal_gain_le",
                "PPT conditioning upper bound",
                "Each party consists of two qubits. Pair an anticommuting Pauli pair and its Hermitian product with their transposes on the other party. The two commuting paired observables give four nonnegative joint projection expectations on the density matrix. Partial transpose supplies the four complementary sign patterns. The sum of the three absolute coefficients is at most one, so the least singular value is at most one twelfth."),
            Theorem("ppt-process-six-bell", "sixBellWitness_attains",
                "An attaining PPT probe",
                "The witness has six equally weighted tensor Bell states. Its partial transpose also has six eigenvalues one sixth and ten zeros. The identity coefficient gives singular value one fourth and every other Pauli coefficient gives one twelfth. The witness is the published six-Bell probe, locally unitarily equivalent to the lattice state of Benatti, Floreanini and Piani."),
            Theorem("ppt-process-physical-minimum", "d4_cptp_attains",
                "Actual channels attain the weakest direction",
                "For each diagonal probe, two distinct completely positive trace-preserving channels with qubit output attain the coefficient of least absolute value. The squared output Hilbert–Schmidt distance equals the squared least gain times the squared distance between their unnormalized Choi matrices."),
            Theorem("ppt-process-spectral-lower", "sixBellWitness_hsSquare_lower",
                "Uniform gain of the attaining probe",
                "For the six-Bell probe, the squared output Hilbert–Schmidt norm of any linear channel difference is at least one over one hundred forty-four times the squared Hilbert–Schmidt norm of its unnormalized Choi matrix. Together with the class upper bound and the channel pair, this yields the sharp worst-direction gain of one twelfth."))));

    private static DocumentBlock Theorem(string id, string name, string title, string prose) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Module + name),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))),
            DescribeRole.Theorem);
}
