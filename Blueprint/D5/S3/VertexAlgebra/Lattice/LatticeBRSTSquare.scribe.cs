using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class LatticeBRSTSquareDocument : IScribeDocumentDefinition
{
    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("latticebrstsquare-" + name.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeBRSTSquare." + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full signed total BRST anomaly", H("The full signed total BRST anomaly"), Blocks(
            Paragraph(Text("The original all-charge lattice carrier is tensored with the original bc occupation Fock space. The total charge is exactly the matter coupling plus the lifted cubic. Ghost degree two and commutation with every b and c mode force the actual square residual to vanish by the charged tensor commutant theorem, which applies to arbitrary matter modules. No scalar-vacuum argument on the matter tensor carrier is used.")),
            Node("total_square_anomaly", "The full operator square", "For every D : LatticeData, H : Matrix (Fin D.rank) (Fin D.rank) Complex, hHG : H * gramComplex D = 1 and hGH : gramComplex D * H = 1, (totalCharge D H)^2 = ((26-(D.rank : Complex))/26) smul ghostSquareAnomaly D. These two inverse-Gram identities are the only extra mathematical hypotheses. The anomaly is the actual lifted native ghost square, not an independently postulated certificate.", DescribeRole.Theorem),
            Node("total_square_finite", "Finite signed support on every tensor state", "For every D : LatticeData and x : State D, the function n : Int maps to (((D.rank : Complex)-26)/24 * ((n : Complex)^3-n)) smul ((ghostC D (-n) * ghostC D n) x) has finite support. Tensor induction extends pure-ghost support to arbitrary finite sums of simple tensors. This is statewise finiteness and makes no claim of finite support in the endomorphism space. No hypothesis on H or on a matter vacuum is used.", DescribeRole.Theorem),
            Node("total_square_apply", "The all-state all-integer signed formula", "For every D : LatticeData, H : Matrix (Fin D.rank) (Fin D.rank) Complex, hHG : H * gramComplex D = 1, hGH : gramComplex D * H = 1, and x : State D, ((totalCharge D H)^2) x equals the finite-support sum over all n : Int of (((D.rank : Complex)-26)/24 * ((n : Complex)^3-n)) smul ((ghostC D (-n) * ghostC D n) x). Scaling the native ghost coefficient -26/24 by (26-rank(D))/26 gives exactly (rank(D)-26)/24. At rank 26 the coefficient vanishes, so the original total charge squares to zero.", DescribeRole.Theorem),
            Paragraph(Text("This algebraic result is a step toward the Monster, VOA/CFT, anomaly and fusion programme. BRST cohomology, the no-ghost theorem, a physical string model and an AdS/CFT correspondence require further constructions.")))));
}
