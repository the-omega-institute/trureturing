using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class FiniteLocalPhysicalGapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The uniform gap for the original finite physical recovery class.",
        H("FiniteLocalPhysicalGap"),
        Blocks(Describe.Lean(
            DescribeId.Create("full-source-finite-recovery-gap"),
            DeclarationHandle.Create("D5/S3/Quantum/Recovery/FiniteLocalPhysicalGap.full_source_finite_recovery_gap"),
            H("Finite CP recovery and the closed-domain source certificate"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Fix the five-ray repeated source with r positive and one half less than r squared less than two. Each physical protocol has its own finite CP instrument tree, arbitrary finite local memories and independent product auxiliary states. Every real terminal history, including failures and early stops, remains in the tree. The acceptance set is fixed on the original actual labels; all histories and hidden terms of one label use its same specified whole-system unitary feedback. Recovery is required on every system matrix. The theorem also retains its equivalence with recovery on every matrix of every finite untouched reference.")),
                Paragraph(Text("Write kappa = sqrt(4 + 2(r squared + r to the power minus two)) / 3, h = 1 / (3(1 + kappa)), g = kappa / (1 + kappa), U = 1 / (3 kappa), Z = 1 - 4 h and H = Z(1 - kappa) / (2 kappa). The original source Bellman value is f = VInfinity on the entire product of closed Bloch balls, with terminal payoff h on K_s and zero elsewhere. Its frontier estimate uses the source tau = H / 4 and epsilon = H squared / 8192.")),
                Paragraph(Text("For every such protocol with nonnegative all-matrix recovery scalar p, the actual normalized input-effect tree gives p at most 4 f at the zero root, and hence p at most U - H cubed / (49152 kappa). The induction uses each actual local trace ratio, its exact actor barycenter and the unchanged inactive Bloch coordinate. A zero effect is treated first: all its descendants have zero effect and reward. Positive nodes use separate concavity. The induction retains the original accepted leaf subset even when other leaves also lie in K_s; it does not replace acceptance by terminal-payoff marking or give abstract trees new physical controls.")),
                Paragraph(Text("The source eta_fin is the real supremum of p over the complete physical finite-protocol class with both all-matrix and untouched-reference recovery and p in [0,1]. Empty acceptance contributes zero, the family is bounded above, and eta_fin is its least upper bound. It is nonnegative and at most 4 f at the zero root, at most U - H cubed / (49152 kappa), strictly below U. These bounds require no common depth, outcome number, memory dimension or minimum positive weight.")),
                Paragraph(Text("At every point of the closed domain, f equals the supremum of all finite one-coordinate barycentric-tree rewards, including immediate stopping. It is separately concave, nonnegative and at most fSEP = d / (3 kappa), equals h on K_s and vanishes on every pure diagonal pair. The function psi = fSEP - f is separately convex, lies between zero and fSEP, vanishes on K_s and on every pure diagonal pair, and at the zero root is at least H cubed / (196608 kappa). The upper bound uses physical-to-abstract domination only; no reverse realization, limiting attainment or limiting regularity is asserted."))),
            DescribeRole.Theorem))));
}
