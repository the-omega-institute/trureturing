using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuTracialSpectatorSqrtEnergyDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuTracialSpectatorSqrtEnergy.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact tracial square-root cell and spectator energy bound on the complex CAR frame.",
        H("Tracial spectator square-root energy"),
        Blocks(
            Paragraph(Text(
                "At spectator ratio 1 in the signed-spin setting of Wu’s cubic trace, the spectator jump is "
                + "J_s = jump 1 = e ⊗ I in occupation order (spectator, cold). Write L_s(A) = A − J_s† A J_s − J_s A J_s†, "
                + "Q = Tr_s(A)/2 and H = A − I ⊗ Q. All traces are ordinary.")),
            Entry("scalar-polynomial-remainder", "scalar_polynomial_identity", "Polynomial identity in the square roots",
                "For all real a,b, (9/8)(a² − b²)²(a² + b²) − (a³ − b³)² = (a − b)⁴(a² + 4ab + b²)/8."),
            Entry("exact-square-root-cell", "sharp_scalar_identity", "Exact square-root cell identity",
                "For all u,v ≥ 0, including zero roots, the tracial cubic cell minus the squared square-root difference is "
                + "(9/8)(u − v)²(u + v) − (u^(3/2) − v^(3/2))² "
                + "= (√u − √v)⁴(u + 4√u√v + v)/8."),
            Entry("tracial-cell-bound", "tracial_cell_lower", "Tracial cubic cell bounds the square-root difference",
                "For u,v ≥ 0, the factorized difference is nonnegative, so cost(1,u,v) ≥ (u^(3/2) − v^(3/2))²."),
            Entry("tracial-trace-excess", "tracial_excess", "Exact spectator trace excess",
                "For every complex Hermitian A, let D = A₀₀ − A₁₁ be the difference of its two diagonal spectator blocks. "
                + "The two gain terms exchange the diagonal blocks, giving Re Tr(A L_s(A)) − Re Tr(H²) = (1/2) Re Tr(D†D)."),
            Entry("tracial-remainder-bound", "remainder_le_tracial", "Remainder bounded by the tracial form",
                "For every Hermitian A, Re Tr(H²) ≤ Re Tr(A L_s(A)) by nonnegativity of the squared Hilbert–Schmidt norm of D."),
            Entry("directed-jump-trace", "tracial_trace_frame", "Quadratic trace on the physical spectator jump",
                "For a complex unitary frame U and real spectral roots v, put sᵢ = vᵢ^(3/2) and A = U diag(s) U†. "
                + "Then Re Tr(A L_s(A)) = ∑ᵢₖ (sᵢ − sₖ)² |(U† J_s U)ᵢₖ|². "
                + "The anticommutator J_s J_s† + J_s† J_s = I gives the two squared terms, and cyclicity of trace identifies the two gain terms."),
            Entry("physical-spectator-energy-bound", "hEs", "Same-frame spectator energy hypothesis",
                "For a complex unitary frame U and nonnegative spectral roots v, set A = U diag(vᵢ^(3/2)) U†. "
                + "Summing the tracial cell inequality with the nonnegative directed weights of J_s gives "
                + "Re Tr(H²) ≤ energy(1,U,1,v). This supplies the energy hypothesis of rankTwo_joint_lower "
                + "for the same square-root matrix and normalized cold marginal."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Wu),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
