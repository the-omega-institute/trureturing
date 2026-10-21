using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class ActualThreeNodeFull336Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual three-node Full336", H("Actual three-node Full336"),
        Blocks(
            Paragraph(Text("K_N is defined to be Matrix.gram Complex (sourceTailFamily hc N n) from the literal source family. It includes every j>=0 and both exterior signs. Its quadratic form is given by actual_source_gram_tsum.")),
            Paragraph(Text("Let delta=9*336*c^2*(1+log(c))^3, l_N=1-delta/N and u_N=(1+delta/N)/(1-(n/N)^2)^2. For c>=3, signed n!=0, N>=9 and |n|<N, the complete actual paired symbol bounds and exact denominator comparison yield l_N H_N <= pi^2 N K_N <= u_N H_N.")),
            Paragraph(Text("The vector form is proved for every complex x, including zero and cancellation, before the Loewner forms. Complete-tail summability holds by actual_tail_summable_all. No vector mass or finite energy is divided out.")),
            Paragraph(Text("The matrices in the two differences are Hermitian by the physical finite-matrix witness and the canonical Gram witness. Their nonnegative quadratic forms give positive semidefiniteness of the two actual differences.")),
            Describe.Lean(DescribeId.Create("delta336"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.delta336"),
                H("delta336"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("def delta336 (c : ℕ) : ℝ := 9 * 336 * (c : ℝ) ^ 2 * (1 + Real.log (c : ℝ)) ^ 3"))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lower336"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.lower336"),
                H("lower336"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("def lower336 (c N : ℕ) : ℝ := 1 - delta336 c / N"))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("upper336"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.upper336"),
                H("upper336"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("def upper336 (c N : ℕ) (n : ℤ) : ℝ :=   (1 + delta336 c / N) / (1 - ((n : ℝ) / N) ^ 2) ^ 2"))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-tail-gram"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actualTailGram"),
                H("actualTailGram"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("def actualTailGram {c : ℕ} (hc : 3 ≤ c) (n : ℤ) (N : ℕ) : Matrix (Fin 3) (Fin 3) ℂ :=   Matrix.gram ℂ (sourceTailFamily hc N n)"))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-full336-all-vector"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_full336_all_vector"),
                H("actual full336 all vector"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem actual_full336_all_vector {c : ℕ} (hc : 3 ≤ c) {n : ℤ} (hn : n ≠ 0)     (N : ℕ) (hN9 : 9 ≤ N) (hR : |(n : ℝ)| < (N : ℝ)) :     ∀ x : Fin 3 → ℂ,       lower336 c N * finiteForm (Real.pi / 4) (mean c)           (arithmeticBoundarySymbol c n) ((n : ℝ) / N) x ≤         Real.pi ^ 2 * N * (star x ⬝ᵥ (actualTailGram hc n N *ᵥ x)).re ∧       Real.pi ^ 2 * N * (star x ⬝ᵥ (actualTailGram hc n N *ᵥ x)).re ≤         upper336 c N n * finiteForm (Real.pi / 4) (mean c)           (arithmeticBoundarySymbol c n) ((n : ℝ) / N) x"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-full336-loewner"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_full336_loewner"),
                H("actual full336 loewner"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem actual_full336_loewner {c : ℕ} (hc : 3 ≤ c) {n : ℤ} (hn : n ≠ 0)     (N : ℕ) (hN9 : 9 ≤ N) (hR : |(n : ℝ)| < (N : ℝ)) :     let H := finiteMatrix (Real.pi / 4) (mean c)       (arithmeticBoundarySymbol c n) ((n : ℝ) / N)     let K := actualTailGram hc n N     ((((Real.pi ^ 2 * N : ℝ) : ℂ) • K) - ((lower336 c N : ℂ) • H)).PosSemidef ∧       (((upper336 c N n : ℂ) • H) - (((Real.pi ^ 2 * N : ℝ) : ℂ) • K)).PosSemidef"))), DescribeRole.Theorem))));
}
