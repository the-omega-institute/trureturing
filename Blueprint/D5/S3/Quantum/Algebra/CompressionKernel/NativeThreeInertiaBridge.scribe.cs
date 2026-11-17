using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.CompressionKernel;

internal sealed class NativeThreeInertiaBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/CompressionKernel/NativeThreeInertiaBridge.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonzero Hermitian compression-kernel form at strict width-three threshold has one positive, one negative, and one zero eigenvalue.", H("Hermitian compression inertia at width three"), Blocks(
            Paragraph(Text("Let a,b : ℕ with a < b. For X : Fin 3 → Matrix (Fin a) (Fin b) ℂ, assume LinearIndependent ℂ X and that (stack X).mulVecLin is injective. If T : Matrix (Fin 3) (Fin 3) ℂ is Hermitian, compression X T = 0, and T ≠ 0, then an equivalence e : Fin 3 ≃ Fin 3 orders its eigenvalues as 0 < eigenvalues(e 0), eigenvalues(e 1) < 0, and eigenvalues(e 2) = 0.")),
            Describe.Lean(DescribeId.Create("spectral-signs"), DeclarationHandle.Create(Prefix + "spectral_signs"), H("The three eigenvalue signs"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The exact conclusion is ∃ e : Fin 3 ≃ Fin 3, 0 < hT.eigenvalues (e 0) ∧ hT.eigenvalues (e 1) < 0 ∧ hT.eigenvalues (e 2) = 0, under the complete telescope hab, X, hX, hinj, T, hT, hPhi, and hne."))), DescribeRole.Theorem))));
}
