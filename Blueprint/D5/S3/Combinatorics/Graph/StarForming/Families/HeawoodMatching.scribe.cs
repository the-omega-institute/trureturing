using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming.Families;

internal sealed class HeawoodMatchingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodMatching.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The same induced matching gives two independent improvements to the Heawood lift bound.",
        H("A parametric matching in binary Heawood lifts"),
        Blocks(
            Describe.Lean(DescribeId.Create("matching-gain"), DeclarationHandle.Create(Prefix + "gain"),
                H("Gain coordinates"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "In the binary Fano coordinates the matrix rows are (v, a, b), (0, 0, c) and (1+v, u, v). " +
                    "The flag signs on (4,1), (4,2), (5,5), (1,2), (1,4) and (2,4) are respectively " +
                    "1, u, v, a, b+v and c. All other signs are zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("matching-beta-bounds"), DeclarationHandle.Create(Prefix + "beta_bounds"),
                H("Dissociation bounds for conjugate gains"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source), Blocks(
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
                        "Gain conjugacy transports this bound to the original lift, where SF=16 also gives beta at most sixteen."))),
                DescribeRole.Theorem))));
}
