using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.ProcessReconstruction;

internal sealed class PPTOperationalGainDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/ProcessReconstruction/PPTOperationalGain.";
    private static readonly LibraryNoteRef Tomography =
        LibraryNoteRef.Create("D5/L/ProcessReconstruction/singh2026boundtomography");
    private static readonly LibraryNoteRef Reduction =
        LibraryNoteRef.Create("D5/L/ProcessReconstruction/horodecki1999reduction");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The least realignment singular value is attained by an actual pair of finite quantum channels.",
        H("Worst-direction gain of quantum process tomography"),
        Blocks(
            Theorem("ppt-operational-minimal-gain", "leastRealignmentSV_sq_isLeast_cptp_gain",
                "The exact weakest gain",
                "For a square Hermitian probe, the minimum ratio of squared output Hilbert–Schmidt distance to squared unnormalized Choi Hilbert–Schmidt distance equals the square of the least realignment singular value. The contraction of a Hermitian probe preserves the adjoint involution on input slices. A least singular direction can therefore be chosen Hermitian. A positive and negative perturbation of the strictly positive depolarizing Choi matrix realizes it by two distinct trace-preserving completely positive maps into a qubit.",
                Tomography),
            Theorem("ppt-operational-marginal-bound", "exists_cptp_pair_weighted_ppt",
                "A marginal-dependent reconstruction bound",
                "For a trace-one PPT probe written in an eigenbasis of its positive second marginal, the same attaining channel pair obeys the upper bound from the marginal spectrum. The construction uses actual channel pairs for each probe covered by the reduction inequality.",
                Reduction))));

    private static DocumentBlock Theorem(string id, string name, string title, string prose,
        LibraryNoteRef source) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Module + name),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(source),
            Blocks(Paragraph(Text(prose))),
            DescribeRole.Theorem);
}
