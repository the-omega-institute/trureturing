using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuTwoTemperatureCubicDeficitDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuTwoTemperatureCubicDeficit.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The physical two-temperature cubic deficit and its conditional same-frame margin.",
        H("Physical two-temperature cubic deficit"),
        Blocks(
            Paragraph(Text(
                "In the unitary frame U, write M = U diag(v) Uᴴ for the matrix of spectral roots. "
                + "The product Gibbs matrix D(R,r) uses ratio r on the left mode and R on the right. "
                + "Its positive sixth root G defines the Gibbs sandwich with X = GInv M GInv.")),
            Entry("reference-row-normalization", "referenceProb_sum", "Gibbs overlap row normalization",
                "The row indexed by spectral column i consists of the nonnegative occupation weights "
                + "referenceProb(U,i,o) = |Uₒᵢ|². The i-th diagonal entry of UᴴU = I gives ∑ₒ referenceProb(U,i,o) = 1."),
            Entry("jump-weight-normalization", "weight_sum", "CAR jump weight normalization",
                "For each jump Jⱼ, the nonnegative weights weight(U,j,i,k) = |(Uᴴ Jⱼ U)ᵢₖ|² sum to 2 over i and k. "
                + "Unitarity identifies the sum with Re Tr(Jⱼᴴ Jⱼ), and the CAR identity Jⱼ Jⱼᴴ + Jⱼᴴ Jⱼ = I "
                + "in dimension four gives twice this trace equal to 4."),
            Entry("entropy-trace", "entropy_eq_operator", "Entropy trace identity",
                "The spectral entropy with the Gibbs log field ∑ₒ |Uₒᵢ|² log Dₒₒ equals "
                + "Re Tr(M³ (cfc Real.log (M³) − cfc Real.log D)) − τ log τ, where τ = Re Tr(M³) = ∑ᵢ vᵢ³. "
                + "The identity includes zero spectral roots."),
            Entry("physical-deficit", "deficit_eq_operator", "Physical deficit identity",
                "For R,r > 0, the spectral deficit with the two actual CAR jump weights and the Gibbs overlap rows "
                + "equals operatorDeficit(R,r,M). Its energy is (9/8) Re Tr(M² G generator(R,r,X) G), "
                + "and the deficit subtracts alpha(R) times the entropy trace."),
            Entry("same-frame-operator-margin", "near_rank_two_operator_deficit", "Conditional same-frame operator margin",
                "Let δ = rankTwoMargin(R), with 1 < R, r ∈ [1,R], 0 ≤ u ≤ v ≤ m ≤ 1, v ≤ ε, "
                + "ε ≤ min(δ/36, (2(1+R³))^(−1/3)), and log r ≤ δ/104. In the same unitary frame U, "
                + "assume the strict tracial rank-two baseline hbase, namely "
                + "δ · mass ![0,0,m,1] < operatorDeficit(R,1,spectralMatrix(U,![0,0,m,1])), with mass ![0,0,m,1] = m³ + 1. "
                + "Then δ/2 < operatorDeficit(R,r,spectralMatrix(U,![u,v,m,1]))."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Wu),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
