using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuTwoTemperatureCubicPhysicalBridgeDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuTwoTemperatureCubicPhysicalBridge.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The physical two-temperature cubic Gibbs bridge for two CAR modes.",
        H("Physical two-temperature cubic bridge"),
        Blocks(
            Paragraph(Text(
                "In occupation order 00, 01, 10, 11, the left mode has ratio r and the right mode has ratio R. "
                + "The one-mode entries are a(t) = 1/(1+t^3) and b(t) = t^3/(1+t^3), so the product Gibbs matrix is "
                + "D(R,r) = d(r) ⊗ₖ d(R), with diagonal entry D_o,o = localEntry(r,o.1) localEntry(R,o.2).")),
            Paragraph(Text(
                "The positive diagonal root G has entry rootEntry(R,r,o) = localRoot(r,o.1) localRoot(R,o.2), where "
                + "localRoot(t,0) = a(t)^(1/6) and localRoot(t,1) = a(t)^(1/6) √t. Thus G^6 = D, G is the real continuous-functional-calculus sixth root of D, and G GInv = GInv G = I.")),
            Entry("jump-gibbs-intertwining", "jump_mul_G", "Matrix jump/Gibbs intertwining",
                "For j in the right-then-left mode order, modeRatio(R,r,j) is R or r. The directed lowering jump satisfies J_j G = √modeRatio(R,r,j) · G J_j, and the adjoint satisfies G J_jᴴ = √modeRatio(R,r,j) · J_jᴴ G. These are the actual matrix identities used by the sandwich."),
            Entry("generator-tracial-split", "generator_eq_cold_add_tracial", "Cold plus tracial generator",
                "At spectator ratio 1, the rates 2a(1) and 2b(1) are both 1. Hence generator(R,1,X) is modeGenerator(R,J₀,X) plus the tracial second-mode dissipator."),
            Entry("mode-trace", "mode_energy_eq_operator", "Physical mode trace",
                "For M = U diag(v) Uᴴ and X = GInv M GInv, the Gibbs-sandwiched operator trace equals the directed energy sum. Each cell is cost(t,x,y) = γ(t)(t x − y)^2(t x + y), weighted by |(Uᴴ J_j U)ᵢₖ|²."),
            Entry("ordinary-cubic-trace", "energy_eq_operator", "Ordinary Wu cubic trace",
                "Summing the right and left mode identities gives energy(R,U,0,v) + energy(r,U,1,v) = (9/8) Re Tr(M² G generator(R,r,GInv M GInv) G). The equality holds for arbitrary real spectral roots, including zero roots."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Wu),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
