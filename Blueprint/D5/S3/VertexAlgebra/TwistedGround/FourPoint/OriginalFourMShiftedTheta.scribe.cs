using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMShiftedThetaDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.";
    private const string Characters = "D5/S3/VertexAlgebra/Characters/";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Source-coupled theta laws in the original mod-two charge sectors",
        H("Doubled Gram sectors and forward modular transformations"),
        Blocks(
            D("original-fourm-doubled-gram", "doubled", "Doubled Gram form",
                DescribeRole.Definition,
                Text("Keep the integral coordinates of D and double its Gram matrix G.")),
            D("original-fourm-discriminant-sector-equivalence", "sectorEquiv",
                "Additive equivalence of charge sectors", DescribeRole.Definition,
                Text("If det G is a unit in ℤ, the mod-two reduction of q corresponds to [Gq] in "
                    + "the Gram cokernel ℤʳ/(2G)ℤʳ. Equality of these classes is equivalent to equality "
                    + "of the mod-two reductions. The dual shift at Gq is q/2.")),
            D("original-fourm-charge-theta", "chargeTheta", "Theta series at an original charge sector",
                DescribeRole.Definition,
                Text("For a mod-two charge a, Θₐ(τ,z) is the shifted theta series at its doubled-Gram "
                    + "class, with complex period τ and complex vector source z.")),
            D("original-fourm-charge-theta-s", "chargeTheta_S", "Forward S with a complex source",
                DescribeRole.Theorem,
                Text("Assume det G is a unit in ℤ, G is positive definite over ℝ, the rank is 24 "
                    + "and Im τ > 0. With Q₂(z) = z · (2Gℂ)z, the theta series at (−1/τ,z/τ) equals "
                    + "(−iτ)¹² exp(πi Q₂(z)/τ) times 2⁻¹² Σᵦ fourierSign(a,b) Θᵦ(τ,z). "
                    + "The doubled-Gram pairing at Gq and Gp is bilinear(D,q,p)/2, which matches "
                    + "the original cocycle sign. Apply "),
                Ref(Characters + "LatticeDiscriminantShiftedTheta.shiftedTheta_S"),
                Text(" and invert its finite Fourier transform using "),
                Ref(Characters + "LatticeDiscriminantWeil.finite_weil_relations"), Text(".")),
            D("original-fourm-theta-charge-fiber", "chargeTheta_eq_charge_sum",
                "Theta series over the integral charge fiber", DescribeRole.Theorem,
                Text("If det G is a unit in ℤ, for every complex τ and z, Θₐ(τ,z) is the topological "
                    + "sum over integral q reducing to a of exp(πiτ bilinear(D,q,q)/2 + 2πi (Gℂq) · z). "
                    + "Here Gℂ denotes the complex cast of G and the dot product is complex bilinear.")),
            D("original-fourm-charge-theta-t", "chargeTheta_T", "Unit translation at fixed source",
                DescribeRole.Theorem,
                Text("If det G is a unit in ℤ and G is positive definite over ℝ, then "
                    + "Θₐ(τ+1,z) = quadraticSign(a) Θₐ(τ,z) for every complex τ and z. "
                    + "The doubled-Gram quadratic class at Gq is represented by bilinear(D,q,q)/4.")))));

    private static DocumentBlock D(string id, string name, string title, DescribeRole role,
        params Inline[] content) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(content)), role);
}
