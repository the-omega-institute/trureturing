using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class LatticeMatterGhostDegreeDocument : IScribeDocumentDefinition
{
    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("latticematterghostdegree-" + name.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostDegree." + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ghost degrees on the original matter tensor carrier", H("Ghost degrees on the original matter tensor carrier"), Blocks(
            Paragraph(Text("For every lattice datum D, the state space is Carrier D tensor the original complex bc occupation Fock space. H is an arbitrary complex matrix indexed by Fin D.rank; no inverse-Gram hypothesis is needed for these degree statements. The number operator acts only on the ghost factor.")),
            Node("tensorNumber", "The tensor number operator", "For every D : LatticeData, tensorNumber D is BcGhostChargeTensor.number with matter module Carrier D, namely the identity on matter tensored with ghostNumber.", DescribeRole.Definition),
            Node("tensorNumber_T", "The matter coupling has degree one", "For every D : LatticeData and H : Matrix (Fin D.rank) (Fin D.rank) Complex, tensorNumber D * T D H - T D H * tensorNumber D = T D H. A common finite capture of x and tensorNumber D x permits the modewise ghost-number identity to be summed on every original tensor state.", DescribeRole.Theorem),
            Node("G", "The lifted cubic", "For every D : LatticeData, G D is the identity on Carrier D tensored with the original cubic Qg.", DescribeRole.Definition),
            Node("Q", "The total matter and cubic charge", "For every D : LatticeData and complex rank-indexed matrix H, Q D H = T D H + G D.", DescribeRole.Definition),
            Node("E", "The square comparison residual", "For every D : LatticeData and complex rank-indexed matrix H, E D H = (Q D H)^2 - ((26-rank(D))/26) smul (G D)^2, with scalars in Complex.", DescribeRole.Definition),
            Node("tensorNumber_G", "The lifted cubic has degree one", "For every D : LatticeData, tensorNumber D * G D - G D * tensorNumber D = G D. The pure ghost cubic degree identity is transported through the actual tensor map.", DescribeRole.Theorem),
            Node("tensorNumber_Q", "The total charge has degree one", "For every D : LatticeData and complex rank-indexed matrix H, tensorNumber D * Q D H - Q D H * tensorNumber D = Q D H. Both summands are the original operators.", DescribeRole.Theorem),
            Node("tensorNumber_E", "The actual residual has degree two", "For every D : LatticeData and complex rank-indexed matrix H, tensorNumber D * E D H - E D H * tensorNumber D = (2 : Complex) smul E D H. The derivation identity for a square applied to the degree-one total and cubic charges proves this without assuming an anomaly formula or a commutant conclusion.", DescribeRole.Theorem),
            Paragraph(Text("This algebraic result is a step toward the Monster, VOA/CFT, anomaly and fusion programme. BRST cohomology, the no-ghost theorem, a physical string model and an AdS/CFT correspondence require further constructions.")))));
}
