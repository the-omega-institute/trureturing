using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Covering;

internal sealed class BinaryAffineGeometryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Covering/BinaryAffineGeometry.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary affine sets cover the plane exactly through six minimal configurations.",
        H("Mixed affine covers of the binary plane"),
        Blocks(
            Paragraph(Text(
                "The points are pairs of binary coordinates. The three nonzero linear forms "
                    + "are x, y and x plus y. An affine shape is empty, the full plane, a level "
                    + "set of one of these forms, or a single point.")),
            Describe.Lean(
                DescribeId.Create("alternatives"), DeclarationHandle.Create(Prefix + "Alternatives"),
                H("The six alternatives"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let F indicate availability of the full plane, L indicate availability of "
                        + "each line, and P indicate availability of each singleton. The alternatives "
                        + "are: F; a complementary parallel pair; the three lines through one point; "
                        + "two distinct directions with their unique missing singleton; a line with "
                        + "both complementary singletons; or all four singletons. These availabilities "
                        + "may be existential predicates over an arbitrary indexed family."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("minimal-patterns"), DeclarationHandle.Create(Prefix + "MinimalCover"),
                H("Minimality by private points"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A finite family is a minimal cover when it covers every point and each "
                        + "member has a point that belongs to no other member. Removing that member "
                        + "therefore leaves a hole. The pattern family uses the omitted direction "
                        + "to label an unordered pair of distinct directions exactly once."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("complete-cover"), DeclarationHandle.Create(Prefix + "mixed_cover_iff"),
                H("Complete mixed-cover identity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every point is covered by an available full plane, line or singleton if "
                            + "and only if one of the six alternatives holds. There are twenty-seven "
                            + "distinct patterns; their shape families are distinct and every pattern "
                            + "is minimal. The six counts are respectively one, three, four, twelve, "
                            + "six and one. Empty sets contribute nothing and repeated events do not "
                            + "change availability.")),
                    Paragraph(Text(
                        "If the lines alone cover, the binary line-cover identity gives a parallel "
                            + "pair or a concurrent triple. Otherwise take a point missed by every "
                            + "line. Two line directions together miss only that point, so its "
                            + "singleton supplies the remaining part. With just one direction and "
                            + "no parallel pair, a line needs its two complementary singletons. "
                            + "Without any lines, all four singletons are necessary. Conversely "
                            + "each listed configuration covers directly; private points establish "
                            + "minimality."))),
                DescribeRole.Theorem)),
        []));
}
