using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class LatticeBRSTWardDocument : IScribeDocumentDefinition
{
    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("latticebrstward-" + name.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard." + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ward identities of the original total BRST charge", H("Ward identities of the original total BRST charge"), Blocks(
            Paragraph(Text("Let D : LatticeData and H : Matrix (Fin D.rank) (Fin D.rank) Complex. All operators act on State D = Carrier D tensor the original countable bc occupation Fock space. B_r, C_r, M_r and V_r denote ghostB D r, ghostC D r, matterMode D H r and ghostVirasoro D r. Brackets below are ordinary commutators and braces are anticommutators. Every mode index ranges over all integers.")),
            Node("ghostCharge", "The lifted original cubic", "For every D, ghostCharge D = TensorProduct.map LinearMap.id BcGhostBRST.Qg.", DescribeRole.Definition),
            Node("totalCharge", "The total original charge", "For every D,H, totalCharge D H = T D H + ghostCharge D. No c-zero or intercept term is added.", DescribeRole.Definition),
            Node("ghostR", "The lifted c Ward operator", "For every D and r : Int, ghostR D r is the identity on matter tensored with BcGhostBRST.R r.", DescribeRole.Definition),
            Node("ghostSquareAnomaly", "The native ghost anomaly on the tensor carrier", "For every D, ghostSquareAnomaly D is the identity on matter tensored with BcGhostBRST.squareAnomaly, the statewise finite signed sum with coefficient (-26/24)(n^3-n).", DescribeRole.Definition),
            Node("total_ward_b", "The b Ward identity", "For every D,H and r : Int, {totalCharge D H, B_r} = M_r + V_r. No inverse-Gram hypothesis is required.", DescribeRole.Theorem),
            Node("total_ward_c", "The c Ward identity", "For every D,H and r : Int, {totalCharge D H, C_r} = ghostR D r. No inverse-Gram hypothesis is required.", DescribeRole.Theorem),
            Node("ghostCharge_square", "Identification of the native ghost square", "For every D, ghostCharge D * ghostCharge D = ghostSquareAnomaly D. This uses the full native ghost square theorem on the original Fock representation.", DescribeRole.Theorem),
            Node("ghostSquareAnomaly_b", "The ghost anomaly b commutator", "For every D and r : Int, [ghostSquareAnomaly D, B_r] = BcGhostBRST.anomalyCoefficient r smul C_r. The coefficient is (26/12)(r^3-r).", DescribeRole.Theorem),
            Node("ghostSquareAnomaly_c", "The ghost anomaly c commutator", "For every D and r : Int, [ghostSquareAnomaly D, C_r] = 0.", DescribeRole.Theorem),
            Node("T_R", "The finite matter and R commutator", "For every D,H and r : Int, [T D H, ghostR D r] = 0. The pure-c CAR gives the modewise relation. One finite capture of x and ghostR D r x extends it to every algebraic tensor state; no operator-family support or matter-vacuum condition is used.", DescribeRole.Theorem),
            Node("total_R", "Commutation with the c Ward operator", "For every D,H and r : Int, [totalCharge D H, ghostR D r] = 0.", DescribeRole.Theorem),
            Node("total_covariance", "The exact rank-dependent covariance", "For every D,H satisfying H * gramComplex D = 1 and gramComplex D * H = 1, and every r : Int, [totalCharge D H, M_r + V_r] = ((26-rank(D))/12)(r^3-r) smul C_r. The matter contribution is minus rank(D)/12 and the cubic ghost contribution is plus 26/12.", DescribeRole.Theorem),
            Node("total_square_b", "The total square b commutator", "For every D,H satisfying the two inverse-Gram identities and every r : Int, [(totalCharge D H)*(totalCharge D H), B_r] = ((26-rank(D))/12)(r^3-r) smul C_r. Associativity identifies this with [Q,{Q,B_r}], with no factor of one half.", DescribeRole.Theorem),
            Node("total_square_c", "The total square c commutator", "For every D,H and every r : Int, [(totalCharge D H)*(totalCharge D H), C_r] = 0. No inverse-Gram hypothesis is required.", DescribeRole.Theorem),
            Node("squareResidual", "The scaled square residual", "For every D,H, squareResidual D H = totalCharge D H * totalCharge D H - ((26-rank(D))/26) smul ghostSquareAnomaly D.", DescribeRole.Definition),
            Node("squareResidual_b", "Commutation of the residual with every b mode", "For every D,H satisfying the two inverse-Gram identities and every r : Int, squareResidual D H * B_r = B_r * squareResidual D H. The native ghost anomaly coefficient cancels the total square coefficient exactly.", DescribeRole.Theorem),
            Node("squareResidual_c", "Commutation of the residual with every c mode", "For every D,H and every r : Int, squareResidual D H * C_r = C_r * squareResidual D H.", DescribeRole.Theorem),
            Paragraph(Text("This algebraic result is a step toward the Monster, VOA/CFT, anomaly and fusion programme. BRST cohomology, the no-ghost theorem, a physical string model and an AdS/CFT correspondence require further constructions.")))));
}
