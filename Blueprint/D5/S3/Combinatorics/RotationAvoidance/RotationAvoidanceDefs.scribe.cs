using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Permutations whose first k rotations avoid a fixed pattern are compared by their cardinalities and the complement and reverse symmetries of patterns of length four.",
        H("RotationAvoidanceDefs"),
        Blocks(
            Node("rotationavoidancedefs-rotationavoiders-definition", "Avoidance in the first k rotations", "rotationAvoiders", "For nonnegative integers n and k and a pattern q, the set S_n^(k)(q) consists of permutations of one through n such that rotating the first i entries to the end avoids q for every nonnegative i less than k. Pattern avoidance is classical avoidance.", DescribeRole.Definition),
            Node("rotationavoidancedefs-wilfequivalent-definition", "Wilf equivalence for a fixed number of rotations", "WilfEquivalent", "Patterns q and s are Wilf-equivalent for k rotations when S_n^(k)(q) and S_n^(k)(s) have equal cardinalities for every nonnegative integer n at least k.", DescribeRole.Definition),
            Node("rotationavoidancedefs-complement-definition", "Complement of a pattern of length four", "complement", "The complement of a pattern of length four replaces each entry x by five minus x, preserving the order of its positions. More generally, this operation is defined on lists of natural numbers using natural-number subtraction.", DescribeRole.Definition),
            Node("rotationavoidancedefs-orbit-definition", "Complement and reverse orbit", "orbit", "The complement and reverse orbit of q is the set consisting of q, its complement, its reverse and the complement of its reverse.", DescribeRole.Definition),
            Node("rotationavoidancedefs-claim-definition", "Statement of Open Question 6.1", "claim", "Open Question 6.1 asks whether, for every integer k at least four and every pair q and s of permutations of one through four, Wilf equivalence for k rotations holds if and only if s belongs to the complement and reverse orbit of q. The proposition expresses the conjectured classification into eight orbits; it does not assert that this classification holds.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
