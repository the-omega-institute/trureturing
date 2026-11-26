using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class WuGibbsThreeCopyDiscriminationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Measurement/WuGibbsThreeCopyDiscrimination.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact three-copy Helstrom bias exceeds every first-qubit PPT payoff for mixed Wu Gibbs rotations with positive Bloch coordinates.",
        H("Three-copy discrimination of Wu Gibbs rotations"),
        Blocks(
            Paragraph(Text(
                "Let ρ(x,z) = (I + zZ + xX)/2 on the active qubit. Write D for the difference " +
                "ρ(x,z)⊗³ − ρ(−x,z)⊗³ and Γ for partial transposition on the first qubit. " +
                "The equal-prior success probability of a binary effect F is (1 + Re tr(FD))/2.")),
            Entry("three-copy-states", "threeCopy_states", "Normalized three-copy hypotheses",
                "For real x and z with x² + z² < 1, both tensor powers are positive definite and have trace one."),
            Entry("three-copy-helstrom", "threeCopy_helstrom", "Exact Helstrom bias and unique effect",
                "For x > 0 and x² + z² < 1, set b = x(√(1 + z² + z⁴) + (1 − x² − z²)/2). " +
                "The Dicke block and two alternating-pair blocks give the sign S(z) of D. The effect P = (I + S(z))/2 " +
                "and its complement are positive semidefinite, Re tr(PD) = b, and the trace norm of D is 2b. " +
                "Every complex binary effect F satisfies Re tr(FD) ≤ b, with equality exactly when F = P."),
            Entry("difference-first-transpose", "difference_firstTranspose", "Invariance of the density difference",
                "For all real x and z, Γ(D) = D because the single-qubit factors are symmetric in the computational basis."),
            Entry("sign-first-transpose-entry", "sign_firstTranspose_entry", "Exact change of the sign entry",
                "Partial transposition exchanges the (000,111) and (100,011) entries. For every real z, " +
                "Re(S[000,111] − S[100,011]) = (2/3)(1 − (1 − z²)/√(1 + z² + z⁴)). " +
                "This difference is positive for z > 0."),
            Entry("three-copy-ppt-lt", "threeCopy_ppt_lt", "Strict PPT payoff bound",
                "For x > 0, z > 0 and x² + z² < 1, if F, I − F, Γ(F) and I − Γ(F) are positive " +
                "semidefinite, then Re tr(FD) < b. Invariance of D gives Γ(F) the same payoff as F. " +
                "Equality would force both effects to equal P by uniqueness, contradicting the change of its " +
                "off-diagonal entry under Γ."),
            Paragraph(Text(
                "Figure 5 of Conlon et al., arXiv:2408.06678v2, includes a numerical comparison of the collective " +
                "Helstrom bound with PPT discrimination across the one-versus-two cut. " +
                "https://arxiv.org/html/2408.06678v2#S4.F5")))));

    private static DocumentBlock Entry(string id, string declaration, string title, string claim) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Wu),
            Blocks(Paragraph(Text(claim))), DescribeRole.Theorem);
}
