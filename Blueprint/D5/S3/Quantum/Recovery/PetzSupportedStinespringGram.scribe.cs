using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class PetzSupportedStinespringGramDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Stinespring complement realizes the upper Petz deficit as a squared Frobenius distance.",
        H("Supported Stinespring amplitudes and ordinary Petz recovery"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("petz-supported-stinespring-gram"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/PetzSupportedStinespringGram.supported_stinespring_gram"),
                H("The completed upper-edge Gram"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/yang2026quantumdataprocessing")),
                Blocks(
                    Paragraph(Text("Take a supported relative modular model for a finite quantum channel Φ and input density states ρ and σ. Let W be an isometric dilation with the environment traced out on the right. At real time t the upper strip exponent is z = 1/2 + it. All matrix powers here are evaluated on the positive spectrum and vanish on the kernel.")),
                    Paragraph(Text("Write Vρ and Vσ for the positive spectral columns of the input states, set U = W Vρ and let Q = Φ(σ) and T = Φ(ρ). In the reference rows the physical factor is K(t) = diag(sʲᶻ) Vσ* W* (Q⁻ᶻ Tᶻ ⊗ I). The completed comparison matrix B(t) adjoins K(t)(I − UU*) to K(t)U diag(r⁻ⁱᵗ). The source matrix A has the mixed supported square-root coordinates in its first block and zero in the environment block.")),
                    Paragraph(Text("The two blocks have Gram sum K(t)K(t)* because the right phase is unitary and the two column projections are complementary. The first block equals the upper modular amplitude. Its missing squared Frobenius norm equals the squared norm of the complementary block, so A and B(t) have unit norm and their squared distance is the upper strip deficit. Under conjugation by Vσ, the Gram of A gives ρ and the Gram of B(0) gives σ¹ᐟ² Φ*(Q⁻¹ᐟ² T Q⁻¹ᐟ²) σ¹ᐟ², with inverse square root zero on the output kernel."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ordinary-petz-rank-trace-error"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/PetzSupportedStinespringGram.ordinary_petz_traceNorm_sq_le_entropy_loss"),
                H("Ordinary Petz trace error from output ranks"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/yang2026quantumdataprocessing")),
                Blocks(
                    Paragraph(Text("For a supported finite channel pair, the ordinary Petz output above has squared physical trace-norm error at most 8 times (1 + rank T · rank Q) times the trace-log entropy loss. A finite exponential expansion counts the constant frequency and at most one frequency for each pair of positive output eigenvalues. The Gram trace estimate acts on the same completed matrices, and support isometry preserves the physical trace norm. The upper integral is bounded by the entropy loss since the lower strip contribution is nonnegative."))),
                DescribeRole.Theorem))));
}
