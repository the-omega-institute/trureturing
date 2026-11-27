using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.ProcessReconstruction;

internal sealed class PPTMarginalBasisDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/ProcessReconstruction/PPTMarginalBasis.";
    private static readonly LibraryNoteRef Reduction =
        LibraryNoteRef.Create("D5/L/ProcessReconstruction/horodecki1999reduction");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Marginal-dependent reconstruction bounds for square PPT probes in any basis.",
        H("Process tomography with arbitrary PPT marginals"),
        Blocks(
            Theorem("ppt-arbitrary-marginal-gain", "exists_cptp_pair_weighted_ppt_of_posDef",
                "A basis-independent physical upper bound",
                "Changing the basis of the reference register conjugates both channel outputs by the same unitary. This preserves their Hilbert–Schmidt distance, the input Choi distance and the exact minimum over channel pairs. Diagonalizing a positive definite reference marginal yields a bound in terms of its eigenvalues on the original probe."),
            Theorem("ppt-singular-marginal-gain", "exists_cptp_pair_zero_gain_of_singular_marginal",
                "Loss of identifiability at a singular marginal",
                "A kernel direction in the reference marginal creates a zero realignment direction for a square positive probe. The physical minimum is attained by two distinct completely positive trace-preserving maps, whose outputs on that probe coincide."))));

    private static DocumentBlock Theorem(string id, string name, string title, string prose) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Module + name),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Reduction),
            Blocks(Paragraph(Text(prose))),
            DescribeRole.Theorem);
}
