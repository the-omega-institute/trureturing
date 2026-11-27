using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming.Families;

internal sealed class HeawoodMatchingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodMatching.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The same induced matching gives two independent improvements to the Heawood lift bound.",
        H("A parametric matching in binary Heawood lifts"),
        Blocks(
            Describe.Lean(DescribeId.Create("matching-gain"), DeclarationHandle.Create(Prefix + "gain"),
                H("Gain coordinates"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For arbitrary u, v, a, b and c in F2, the matrix rows in binary Fano coordinates are " +
                    "(v, a, b), (0, 0, c) and (1+v, u, v). " +
                    "The flag signs on (4,1), (4,2), (5,5), (1,2), (1,4) and (2,4) are respectively " +
                    "1, u, v, a, b+v and c. All other signs are zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("matching-beta-bounds"), DeclarationHandle.Create(Prefix + "beta_bounds"),
                H("Dissociation bounds for conjugate gains"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text(
                        "Let s be any signing and let g be an invertible binary matrix. For any u, v, a, b and c in F2, " +
                        "suppose Phi(s) = g gain(u,v,a,b,c) g⁻¹. Then beta(graph(s),2) is at least fourteen plus one " +
                        "if u=0 and one if u+v=1, and beta(graph(s),2) is at most sixteen.")),
                    Paragraph(Text(
                        "Select point lifts 2_0, 2_1, 3_0, 3_1, 4_0, 5_(1+u), 6_1 and 7_0. " +
                        "The six fixed line lifts 1_0, 2_u, 2_(1+u), 3_1, 6_1 and 6_0 have unique selected " +
                        "neighbors 2_0, 4_0, 5_(1+u), 3_1, 6_1 and 7_0 respectively.")),
                    Paragraph(Text(
                        "When u=0, line lift 7_0 has 3_0 as its unique selected neighbor. " +
                        "When u+v=1, line lift 5_1 has 2_1 as its unique selected neighbor. " +
                        "The flag signs involving a, b and c do not affect these neighbor relations. " +
                        "Each selected line has a distinct selected point as its neighbor, so the selected graph " +
                        "has maximum degree one. Its order is fourteen plus one for each of the two conditions. " +
                        "HeawoodMatrixAction.isomorphic_of_phi_conjugate transports this bound to the original lift, " +
                        "where SF=16 also gives beta at most sixteen."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The Fano flag coordinates, binary sheet rule and gain conjugacy are from the subquorum-colorings " +
                "contributors under Apache-2.0. The conjugacy step uses the existing formalization in HeawoodMatrixAction. " +
                "https://github.com/the-omega-institute/subquorum-colorings/blob/48728b42d39ab3de5de251c61da5a404ec418a69/docs/HEAWOOD_DOUBLE_COVER_GAIN.md#L26-L66")))));
}
