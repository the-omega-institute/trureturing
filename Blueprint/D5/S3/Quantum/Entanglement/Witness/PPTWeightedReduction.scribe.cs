using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Witness;

internal sealed class PPTWeightedReductionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Entanglement/Witness/PPTWeightedReduction.";
    private static readonly LibraryNoteRef Reduction =
        LibraryNoteRef.Create("D5/L/ProcessReconstruction/horodecki1999reduction");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Marginal-dependent bounds on the least realignment singular value of a PPT probe.",
        H("Marginal bounds for PPT process tomography"),
        Blocks(
            Theorem("ppt-reduction-by-skew", "le_alice_identity_kron_marginal_of_ppt",
                "The reduction inequality",
                "The transpose-composed reduction map is a sum of congruences by antisymmetric matrix units. Applying it to the partially transposed probe bounds the original probe above by the first identity tensored with the second marginal."),
            Theorem("ppt-weighted-singular-value", "weighted_converse_of_ppt",
                "The marginal controls the least detectable direction",
                "For an equal-dimensional probe in the eigenbasis of its positive second marginal, the upper bound on the squared least realignment singular value is the dimension minus one divided by the dimension squared times the inverse marginal trace minus one. The weighted trace bound comes from the reduction criterion. The normalized identity direction contributes the additional trace term."),
            Theorem("ppt-singular-marginal", "leastRealignmentSV_eq_zero_of_marginal_entry_eq_zero",
                "A zero marginal entry forces zero gain",
                "A vanishing diagonal entry of a marginal of a positive matrix forces the corresponding block row and block column of the probe to vanish. The square realignment then has a zero singular value."))));

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
