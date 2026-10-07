using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Construction;

internal sealed class ScalingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Construction/Scaling.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Construction A lattices, covolumes and ellipsoid transfer.",
        H("Scaling"),
        Blocks(
            Paragraph(Text("Construction A lattices, covolumes and ellipsoid transfer. The results below relate scaling to the stochastic ellipsoid construction.")),
            Node("claim-1", "ereal_rhs", "ereal rhs",
                "The quadratic target volume agrees whether its multiplication is performed in the reals before coercion or directly in the extended reals.", DescribeRole.Theorem),
            Node("claim-2", "ereal_coe_volume_eq", "ereal coe volume eq",
                "A finite measure equal to ofReal r has extended-real value r when r is nonnegative.", DescribeRole.Theorem),
            Node("claim-3", "volume_image_ball", "volume image ball",
                "The volume of a linear image of the unit ball is the absolute determinant of the map times the unit-ball volume, including singular maps.", DescribeRole.Theorem),
            Node("claim-4", "volume_image_ball_ne_top", "volume image ball ne top",
                "A linear image of the unit ball in finite-dimensional Euclidean space has finite volume.", DescribeRole.Theorem),
            Node("claim-5", "smul_image_ball_subset", "smul image ball subset",
                "Multiplying a linear map by a scalar of absolute value at most one shrinks its unit-ball image inside the original image.", DescribeRole.Theorem),
            Node("claim-6", "volume_smul_image_ball", "volume smul image ball",
                "Scaling a linear map by a nonnegative scalar t multiplies its unit-ball image volume by t^(n+1).", DescribeRole.Theorem),
            Node("claim-7", "exists_volume_eq_of_le", "exists volume eq of le",
                "An ellipsoid that contains no nonzero integer point can be shrunk to any positive target volume at most its own volume, preserving the exact singleton integer-point set.", DescribeRole.Theorem),
            Node("claim-8", "image_zero_ball", "image zero ball",
                "The zero linear map sends the open unit ball to the singleton zero.", DescribeRole.Theorem),
            Node("claim-9", "case_zero", "case zero",
                "The zero map gives the required volume and integer-point set at n=0 for every real packing coefficient.", DescribeRole.Theorem),
            Node("claim-10", "klartag_of_volume_ge", "klartag of volume ge",
                "A uniform quadratic lower volume bound in every positive natural dimension gives the exact quadratic volume theorem by shrinking; the zero dimension parameter uses the zero map.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
