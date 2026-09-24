using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Covering;

internal sealed class PairedEightRowsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Covering/PairedEightRows.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Eight affine congruence rows with shared phases leave a horizontal deficit across "
            + "paired fibers. Separate successful repairs need not have a common phase vector.",
        H("Shared phases across paired eight-row fibers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("guarded-transition"),
                DeclarationHandle.Create(Prefix + "Admissible"),
                H("Guarded rows and their transition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The four rows modulo eight are y=a, 6x+y=b, x+6y=u and x+2y=v. "
                        + "The four rows modulo four are 2x+y=s, 3x=f, 2x+y=t and y=h. "
                        + "Each right side can be inactive. Across the pair, a and h remain "
                        + "fixed, b and s increase by one, and t increases by three. These "
                        + "five rows preserve their activation status. Each of u, v and f is "
                        + "active on at most one side; both-inactive cases are allowed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("full-parity-class"),
                DeclarationHandle.Create(Prefix + "full"),
                H("Full parity classes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A parity class (i,j) is full precisely when all sixteen positions "
                        + "(i+2r,j+2s), for r and s from zero through three, are covered by "
                        + "the eight guarded rows. J denotes the full classes supplied by "
                        + "the horizontal rows alone. W consists of the full classes outside J."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("paired-horizontal-bound"),
                DeclarationHandle.Create(Prefix + "paired_bound"),
                H("The paired horizontal deficit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every admissible pair, W is nonempty on at most one side. "
                            + "On each side all its points have the same first parity coordinate. "
                            + "For either horizontal parity j, the two J intersections have "
                            + "total cardinality at most two, and the two full intersections "
                            + "have total cardinality at most three. Consequently completion "
                            + "of one side by a horizontal line excludes completion of the "
                            + "other side by that same line.")),
                    Paragraph(Text(
                        "The first descent derives complementary parents A and B from the "
                            + "four literal equations modulo eight. A full class outside J "
                            + "needs two distinct resources among A, B and f: the missing "
                            + "horizontal position occurs in both columns, and any one resource "
                            + "can fill only one column. Each resource occupies one first "
                            + "parity coordinate and at most one side. Any two pairs drawn "
                            + "from three resources intersect, which forces W's exclusion and "
                            + "vertical alignment. The horizontal carry relation bounds J; "
                            + "combining the two contributions gives three."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-rows"),
                DeclarationHandle.Create(Prefix + "original"),
                H("The eight original congruences"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In prime order 257, 3329, 7681, 15361, 641, 769, 1409, 4481, the "
                        + "triples (modulus, first coefficient, second coefficient) are "
                        + "(256,48,1), (3328,1134,1), (3840,2273,3534), (3840,2257,3762), "
                        + "(640,470,1), (384,139,232), (1408,58,1) and (4480,3112,1). "
                        + "The original phase vector has eight unrestricted integer entries. "
                        + "Rows use the original affine divisibility predicate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("original-paired-bound"),
                DeclarationHandle.Create(Prefix + "original_bound"),
                H("All integer basepoints and original phases"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Q=16865820972000. At every integer basepoint (k,l), a parity "
                            + "class consists of the sixteen original positions "
                            + "(k+Q(i+2r),l+Q(j+2s)). Its full-coverage predicate equals the "
                            + "guarded local predicate. The local phase is computed from the "
                            + "Euclidean residue of c-ak-bl, with the activation guard retained. "
                            + "The eight activation divisors are 32, 416, 480, 480, 160, 96, "
                            + "352 and 1120. Their inverse multipliers are 7, 3, 1, 1, 3, 1, "
                            + "1 and 1 in their respective local moduli.")),
                    Paragraph(Text(
                        "The same original phase vector at (k,l) and (k+Q/2,l) produces an "
                            + "admissible pair. Literal original-row full intersections with "
                            + "either horizontal parity therefore have total cardinality at "
                            + "most three. Completion of the first by a horizontal line "
                            + "excludes completion of the second by the same line. Negative "
                            + "basepoints and arbitrary integer phase representatives are "
                            + "included; no phase is chosen anew at a basepoint."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("independent-repair-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Independent repair assertion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The assertion says that separate successful original-phase completions "
                        + "at zero and at (Q/2,0), both using the line y=1, imply a common "
                        + "successful eight-phase vector for the two fibers."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("independent-repair-refutation"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Separate repairs cannot be assembled"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The assertion is false. The vector (0,0,0,0,0,0,704,0) gives mask "
                            + "7 at zero, and (0,0,0,0,160,0,1056,0) gives mask 5 at (Q/2,0). "
                            + "Mask bit 2i+j represents (i,j). Each mask contains the entire "
                            + "line y=0, so y=1 completes its fiber. A common vector would "
                            + "give four full classes of horizontal parity zero, violating "
                            + "the original paired bound.")),
                    Paragraph(Text(
                        "These conclusions concern only the specified eight rows. The "
                            + "285-row cover, the condition on the other 277 phases, the "
                            + "ordinary and ternary rescue branches, and the whole Erdős "
                            + "203 assertion are not established here."))),
                DescribeRole.Theorem)),
        []));
}
