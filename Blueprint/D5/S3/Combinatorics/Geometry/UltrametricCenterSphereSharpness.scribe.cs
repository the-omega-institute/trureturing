using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class UltrametricCenterSphereSharpnessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/UltrametricCenterSphereSharpness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The pointwise counts one, two and four at central radii zero, one and two force order eight and two distinct lower-gap distances; every prescribed pair attains the bound without an upper-gap distance.",
        H("Two lower-gap distances are necessary and sufficient"),
        Blocks(
            Describe.Lean(DescribeId.Create("order-and-gap-lower-bound"),
                DeclarationHandle.Create(Prefix + "order_eight_and_two_gap_distances"),
                H("Every realization has order eight and two distinct distances below one"),
                StatementSource.FromAuthor(Disp(Seq(Call("card", F.Id("X")), Sp, Eq, Sp, D(8), Sp, Land, Sp,
                    Exists, Sp, F.Id("p"), Comma, F.Id("q"), Comma, F.Id("r"), Comma, F.Id("s"),
                    Colon, F.Id("X"), Comma, Sp, Gap(Call("dist", F.Id("p"), F.Id("q"))),
                    Sp, Land, Sp, Gap(Call("dist", F.Id("r"), F.Id("s"))), Sp, Land, Sp,
                    Call("dist", F.Id("p"), F.Id("q")), Sp, Neq, Sp, Call("dist", F.Id("r"), F.Id("s"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let X be an arbitrary finite nonempty metric space with IsUltrametricDist. Assume its original distance center is exactly the real set consisting of zero, one and two, and assume every sphere at one has two points and every sphere at two has four points. Then the displayed conjunction holds. The zero sphere automatically has one point. No distance-support restriction or preselected gap pair is assumed in this lower bound.")),
                    Paragraph(Text("The recurrence forces order eight. Partitioning the strict ball at two into closed balls at one forces each point to have a neighbor at a distance strictly between zero and one. A single such distance common to all points would be central; the center equality rules this out and yields two distinct gap distances."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exact-sharp-support"), DeclarationHandle.Create(Prefix + "eight_exact_distance_values"),
                H("Every prescribed lower-gap pair gives exactly the five distance values"),
                StatementSource.FromAuthor(Disp(Seq(Call("range", Seq(LambdaLower, Sp, Langle, Sp,
                    F.Id("p"), Comma, F.Id("q"), Rangle, Sp, Mapsto, Sp, Call("dist", F.Id("p"), F.Id("q")))),
                    Sp, Eq, Sp, OpenBrace, D(0), Comma, F.Id("u"), Comma, F.Id("v"), Comma, D(1), Comma, D(2), CloseBrace))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary real u and v satisfying "),
                    Math(In(Seq(D(0), Sp, Lt, Sp, F.Id("u"), Sp, Lt, Sp, F.Id("v"), Sp, Lt, Sp, D(1)))),
                    Text(", p and q range over Eight u v hu huv hv. The equality states exact occurrence of all five displayed values, not merely containment. The eight-point module establishes its order, exact original center and every sphere count via "),
                    Ref("D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.eight_card"), Text(", "),
                    Ref("D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.eight_center"), Text(", "),
                    Ref("D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.sphere_zero_card"), Text(", "),
                    Ref("D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.sphere_one_card"), Text(" and "),
                    Ref("D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.sphere_two_card"), Text(".")),
                    Paragraph(Text("Together these declarations attain the lower bound with the two fixed lower-gap distances and no distance strictly between one and two. They do not assert that two auxiliary values are necessary in every gap of every count sequence."))),
                DescribeRole.Theorem))));

    private static Formula Gap(Formula distance) => Seq(D(0), Sp, Lt, Sp, distance, Sp, Lt, Sp, D(1));
}
