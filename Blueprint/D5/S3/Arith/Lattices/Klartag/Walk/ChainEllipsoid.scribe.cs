using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Walk;

internal sealed class ChainEllipsoidDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Walk/ChainEllipsoid.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian matrix walk, filtration and stopped increments.",
        H("Chain Ellipsoid"),
        Blocks(
            Paragraph(Text("Gaussian matrix walk, filtration and stopped increments. The results below relate chain ellipsoid to the stochastic ellipsoid construction.")),
            Node("claim-1", "ellipsoid", "ellipsoid",
                "E_A = {v | ⟪A v, v⟫ < 1}, Klartag eq. (9).", DescribeRole.Definition),
            Node("claim-2", "det_sq_mul_det", "det sq mul det",
                "Sᵀ A S = 1 forces det(S)² det(A) = 1; in particular S is invertible.", DescribeRole.Theorem),
            Node("claim-4", "quad_congr", "quad congr",
                "The congruence identity for the quadratic form.", DescribeRole.Theorem),
            Node("claim-7", "image_ball_eq_ellipsoid", "image ball eq ellipsoid",
                "Klartag eq. (9): the ellipsoid is the image of the unit ball.", DescribeRole.Theorem),
            Node("claim-8", "volume_ellipsoid", "volume ellipsoid",
                "Klartag eq. (10): Vol(E_A) = det(A)^{-1/2} Vol(Bⁿ).", DescribeRole.Theorem),
            Node("claim-9", "volume_ellipsoid_ge", "volume ellipsoid ge",
                "Klartag eq. (68). If √(det A) · D ≤ Vol(Bⁿ) then the ellipsoid has volume at least D. The chain supplies det A_T ≤ C/n⁴, i.e. D = c n².", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
