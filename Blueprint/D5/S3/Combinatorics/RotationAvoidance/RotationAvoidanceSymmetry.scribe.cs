using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceSymmetryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceSymmetry.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complement and reverse preserve the cardinalities of permutation classes defined by avoidance in the first k rotations.",
        H("RotationAvoidanceSymmetry"),
        Blocks(
            Node("rotationavoidancesymmetry-orbit-wilfequivalent-theorem", "Wilf equivalence within an orbit", "orbit_wilfEquivalent", "For every positive integer k, every permutation q of one through four and every pattern s in the complement and reverse orbit of q, the patterns q and s are Wilf-equivalent for k rotations. Thus S_n^(k)(q) and S_n^(k)(s) have equal cardinalities for every n at least k.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
