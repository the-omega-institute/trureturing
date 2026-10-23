using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;
internal sealed class UniformSchmidtVarianceConsumerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact independent assignment moments apply to the literal Bell family produced by one APPT spectrum. Singular PSD matrices and zero pool variances are included. Rank two uses its singleton top pool separately; larger ranks use the general incidence moments.", H("UniformSchmidtVarianceConsumer"), Blocks(
            Paragraph(Text("Exact independent assignment moments apply to the literal Bell family produced by one APPT spectrum. Singular PSD matrices and zero pool variances are included. Rank two uses its singleton top pool separately; larger ranks use the general incidence moments.")),
            Describe.Lean(DescribeId.Create("uniformschmidtvarianceconsumer-bottom-pos"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtVarianceConsumer.bottom_pos"),
                H("bottom pos"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem bottom_pos {r : ℕ} (hr : 2 ≤ r) : 0 < b r"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniformschmidtvarianceconsumer-variance"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtVarianceConsumer.variance"),
                H("variance"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("def variance {k : ℕ} (z : Fin k → ℝ) : ℝ"))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("uniformschmidtvarianceconsumer-momentlhs"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtVarianceConsumer.momentLHS"),
                H("momentLHS"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("def momentLHS {r N : ℕ} (hN : a r + b r ≤ N) (l : Fin N → ℝ) : ℝ"))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("uniformschmidtvarianceconsumer-momentrhs"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtVarianceConsumer.momentRHS"),
                H("momentRHS"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("def momentRHS {r N : ℕ} (hN : a r + b r ≤ N) (hb : 0 < b r) (l : Fin N → ℝ) : ℝ"))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("uniformschmidtvarianceconsumer-literal-r2-variance-moment"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtVarianceConsumer.literal_r2_variance_moment"),
                H("literal r2 variance moment"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem literal_r2_variance_moment {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (e : (Fin m × Fin n) ≃ Fin (m * n)) (l : Fin (m * n) → ℝ) (hl : Antitone l) (h : APPT (diagonal (fun p => (l (e p) : ℂ)))) : let hN : a 2 + b 2 ≤ m * n := (pool_card_sum 2).trans_le (Nat.mul_le_mul hm hn) momentLHS hN l ≤ momentRHS hN (bottom_pos (by norm_num)) l"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniformschmidtvarianceconsumer-literal-variance-moment"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtVarianceConsumer.literal_variance_moment"),
                H("literal variance moment"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem literal_variance_moment {r m n : ℕ} (hr : 2 ≤ r) (hm : r ≤ m) (hn : r ≤ n) (e : (Fin m × Fin n) ≃ Fin (m * n)) (l : Fin (m * n) → ℝ) (hl : Antitone l) (h : APPT (diagonal (fun p => (l (e p) : ℂ)))) : let hN : a r + b r ≤ m * n := (pool_card_sum r).trans_le (Nat.mul_le_mul hm hn) momentLHS hN l ≤ momentRHS hN (bottom_pos hr) l"))), DescribeRole.Theorem)
        )));
}
