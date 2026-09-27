using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Covering;

internal sealed class BinaryCarryQuotientDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Covering/BinaryCarryQuotient.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A periodic family of affine congruence rows descends through a binary quotient "
            + "by retaining activation, direction and carry for the same original phases.",
        H("Binary carry and phase-preserving quotient coverage"),
        Blocks(
            Paragraph(Text(
                "Fix a positive integer M and period N equal to twice M. A row has positive "
                    + "modulus e dividing N, integer coefficients a and b, and an arbitrary "
                    + "integer phase c. The rows may be indexed by any type, including an empty "
                    + "type. Thus the results apply to every finite family without requiring "
                    + "distinct moduli or distinct congruence classes.")),
            Describe.Lean(
                DescribeId.Create("original-row"),
                DeclarationHandle.Create(Prefix + "covers"),
                H("The original affine congruence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A row covers the integer pair (k,l) exactly when e divides a k plus b l "
                        + "minus c. Equivalently, a k plus b l is congruent to c modulo e. "
                        + "The phase belongs to the row and is shared by every occurrence "
                        + "of that row in the quotient predicates."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("scaled-form"),
                DeclarationHandle.Create(Prefix + "scaled"),
                H("Scaling to the common period"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Write F for N/e times the original affine expression. Divisibility "
                        + "by e of the original expression is equivalent to divisibility of "
                        + "F by N. A top row is exactly a row for which N/e is odd. Its normal "
                        + "is the pair (a modulo 2, b modulo 2); its activity at a basepoint "
                        + "means divisibility of F by M. Every top normal is assumed nonzero. "
                        + "This is the only consequence of primitivity needed here."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quotient-criterion"),
                DeclarationHandle.Create(Prefix + "Criterion"),
                H("Three ways to cover a binary fiber"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The first alternative is a lower row covering the basepoint. "
                            + "A lower row is precisely a row outside the top cohort.")),
                    Paragraph(Text(
                        "The second is a pair of distinct top indices with equal normals. "
                            + "Both rows must be active, and their two scaled values must "
                            + "sum to M modulo N. These are complementary parallel lines.")),
                    Paragraph(Text(
                        "The third is a triple of top rows whose normals are pairwise "
                            + "distinct. All three rows must be active, and their scaled "
                            + "values must sum to zero modulo N. The nonzero-normal hypothesis "
                            + "makes these exactly the three nonzero binary directions and "
                            + "also forces the three indices to be distinct."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("binary-plane"),
                DeclarationHandle.Create(Prefix + "plane_cover_iff"),
                H("Covering the four-point plane"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "An arbitrary active family of lines with nonzero binary normals "
                            + "covers the plane exactly when it contains a complementary "
                            + "parallel pair or a triple of distinct directions with even "
                            + "carry sum. Inactive indices impose no normal constraint.")),
                    Paragraph(Text(
                        "There are two possible lines in each of the horizontal, vertical "
                            + "and diagonal directions. The four point-covering conditions "
                            + "select either a complementary pair or one of the four concurrent "
                            + "triples. Conversely, a complementary pair covers directly. "
                            + "For a distinct-direction triple, each coordinate of the normal "
                            + "sum is two; three failed line equations would have odd sum, "
                            + "contradicting the even carry sum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("phase-preserving-descent"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Exact descent with unchanged phases"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every integer basepoint, all four lifts obtained by adding M "
                            + "times a binary pair are covered if and only if the quotient "
                            + "criterion holds. The criterion is invariant under adding M "
                            + "times any integer pair to the basepoint. Coverage of the square "
                            + "from zero inclusive to M exclusive by this criterion is "
                            + "equivalent both to original-row coverage of every integer "
                            + "pair and to original-row coverage of the period-N square.")),
                    Paragraph(Text(
                        "On a lift, the scaled form changes by M times N/e times the normal "
                            + "dot the lift coordinates. An even N/e makes the row constant "
                            + "on the fiber. For odd N/e, coverage first requires activity; "
                            + "after division by M, the equation is the binary line equation "
                            + "with carry F/M modulo 2. Cancellation of M gives the stated "
                            + "pair and triple congruences. Reducing arbitrary integer lift "
                            + "coordinates modulo two proves representative invariance; "
                            + "Euclidean division supplies every basepoint in the finite quotient.")),
                    Paragraph(Text(
                        "The theorem gives an equivalence for each fixed original phase "
                            + "assignment. It asserts no existence of a covering assignment. "
                            + "A compressed event whose next fiber is a point does not satisfy "
                            + "the line hypotheses automatically; a further descent requires "
                            + "a separate description of that event."))),
                DescribeRole.Theorem)),
        []));
}
