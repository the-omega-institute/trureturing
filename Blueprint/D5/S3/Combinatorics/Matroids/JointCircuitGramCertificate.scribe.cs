using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class JointCircuitGramCertificateDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/JointCircuitGramCertificate";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed circuit restriction is adjoint to oriented join and has an exact integral image certificate.",
        H("The joint integral image of signed circuit restriction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("joint-circuit-gram-certificate"),
                DeclarationHandle.Create(Module + ".joint_circuit_gram_certificate"),
                H("Signed adjointness and the joint Gram certificate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let M be a matroid on a finite linearly ordered carrier and fix any element e "
                        + "of its ground set. Use the ordinary integer dot product over all finite face "
                        + "coordinates. For each circuit K, the signed restriction at a vertex a of K "
                        + "reads the coefficient on the union of a contraction basis and the facet "
                        + "obtained by deleting a. Its sign is the boundary sign of that facet times "
                        + "the shuffle sign for the facet followed by the contraction basis. "
                        + "Write A for the sum of these restrictions on K and L for the signed join "
                        + "with the oriented augmented boundary of the simplex on K.")),
                    Paragraph(Text(
                        "For each circuit K, every integral augmented top cycle z of M and every "
                        + "integral augmented top cycle w of the contraction satisfy the adjoint "
                        + "identity pairing A applied to z with w and pairing z with L applied to w. "
                        + "Only faces whose intersection with K is a circuit facet and whose difference "
                        + "with K is a contraction basis contribute. The intersection identifies the "
                        + "deleted vertex, and the difference identifies the contraction basis. This "
                        + "bijection preserves the signed summands.")),
                    Paragraph(Text(
                        "Index G by the internally passive bases of M, with each entry the pairing "
                        + "of the two normalized integral cycles. Its determinant is nonzero and "
                        + "equals one when the index set is empty. For any tuple y of contracted "
                        + "top cycles indexed by all circuits, define b at a passive basis B by "
                        + "summing, over circuits containing e, the pairing of the corresponding "
                        + "entry of y with the signed restriction at e of the normalized cycle at B.")),
                    Paragraph(Text(
                        "The tuple y has a unique integral top cycle z satisfying all its aggregate "
                        + "restrictions if and only if both conditions hold. For every circuit K "
                        + "and every passive basis T of its contraction, the pairing of the K entry "
                        + "of y with the normalized cycle at T equals the sum over passive bases B "
                        + "of M of b at B times the B coefficient of the join of that normalized "
                        + "cycle with the boundary on K. Also, the determinant of G divides every "
                        + "coordinate of the adjugate of G applied to b.")),
                    Paragraph(Text(
                        "The signed pivot decomposition reconstructs each normalized source cycle "
                        + "as a sum of joins over circuits containing e. Adjointness then identifies "
                        + "b with its pairings against a lift. The normalized cycles give integral "
                        + "coordinates and make G positive definite. The adjugate identity gives "
                        + "integral coordinates for the lift under the divisibility condition. "
                        + "The compatibility equalities determine each contracted cycle by its "
                        + "pairings with the normalized cycles, and the source pairings determine "
                        + "the lift uniquely."))),
                DescribeRole.Theorem))));
}
