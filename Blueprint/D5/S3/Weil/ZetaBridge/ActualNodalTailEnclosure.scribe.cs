using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class ActualNodalTailEnclosureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Nodal Infinite Tail Enclosure", H("Actual Nodal Infinite Tail Enclosure"),
        Blocks(
            Paragraph(Text("The nodal numerator and denominator are exactly ActualNodalCoercivity.P, Q and D. The actual couplingColumn is rewritten through their existing common-denominator identity. No substitute model is introduced.")),
            Paragraph(Text("Assume c>=3, a finite nonempty set S of integer nodes, d=card(S), d^2<=N, a real B>=0 with 2*B<=N, and abs(n)<=B at every head node. Both nodal factors are positive: 1-B/N>0 and 1+B/N>0. Every complex vector v is allowed.")),
            Paragraph(Text("Let A and Q be the reciprocal polynomials of the actual nodal P and Q and H their pairedEnergy. The sum of norm(couplingColumn(m))^2+norm(couplingColumn(-m))^2 over all m>N is summable and lies between (1-epsilon)*H/[pi^2*N*(1+B/N)^(2*d)] and (1+epsilon)*H/[pi^2*N*(1-B/N)^(2*d)], with epsilon=d^2*U(c)/N.")),
            Paragraph(Text("For every eta>0 there exists one natural N0 before the quantifier over all v, and these bounds hold with eta at every N>=N0. The cutoff enforces the dimension, radius and relative-error constraints simultaneously. Both epsilon comparisons use H>=0, including H=0; no coefficient-dependent cutoff or energy division is used.")),
            Describe.Lean(DescribeId.Create("paired-column-term"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/ActualNodalTailEnclosure.pairedColumnTerm"),
                H("pairedColumnTerm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Lean defining declaration: def pairedColumnTerm (c N : ℕ) (S : Finset ℤ) (v : ℤ → ℂ) (j : ℕ) : ℝ := ‖couplingColumn c S v ((N+j+1:ℕ):ℤ)‖^2+ ‖couplingColumn c S v (-((N+j+1:ℕ):ℤ))‖^2."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-paired-column-enclosure"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/ActualNodalTailEnclosure.actual_paired_column_enclosure"),
                H("actual paired column enclosure"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete Lean telescope and conclusion: theorem actual_paired_column_enclosure {c N : ℕ} (hc : 3 ≤ c) (S : Finset ℤ) (hSne : S.Nonempty) (v : ℤ → ℂ) (hNdim : S.card^2 ≤ N) {B : ℝ} (hB : 0 ≤ B) (hBN : 2*B ≤ N) (hS : ∀ n ∈ S, |(n:ℝ)| ≤ B) : let d := S.card let A := reciprocalPolynomial d N (ActualNodalCoercivity.P c S v) let Q := reciprocalPolynomial d N (ActualNodalCoercivity.Q S v) let H := pairedEnergy c A Q let ε := (d:ℝ)^2*U c/(N:ℝ) Summable (pairedColumnTerm c N S v) ∧ (1-ε)*H/(Real.pi^2*(N:ℝ)*(1+B/(N:ℝ))^(2*d)) ≤ (∑' j : ℕ,pairedColumnTerm c N S v j) ∧ (∑' j : ℕ,pairedColumnTerm c N S v j) ≤ (1+ε)*H/(Real.pi^2*(N:ℝ)*(1-B/(N:ℝ))^(2*d))."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-paired-column-uniform-enclosure"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/ActualNodalTailEnclosure.actual_paired_column_uniform_enclosure"),
                H("actual paired column uniform enclosure"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete Lean telescope and conclusion: theorem actual_paired_column_uniform_enclosure {c : ℕ} (hc : 3 ≤ c) (S : Finset ℤ) (hSne : S.Nonempty) {B : ℝ} (hB : 0 ≤ B) (hS : ∀ n ∈ S, |(n:ℝ)| ≤ B) {η : ℝ} (hη : 0 < η) : ∃ N0 : ℕ, ∀ v : ℤ → ℂ, ∀ N : ℕ, N0 ≤ N → let d := S.card let A := reciprocalPolynomial d N (ActualNodalCoercivity.P c S v) let Q := reciprocalPolynomial d N (ActualNodalCoercivity.Q S v) let H := pairedEnergy c A Q Summable (pairedColumnTerm c N S v) ∧ (1-η)*H/(Real.pi^2*(N:ℝ)*(1+B/(N:ℝ))^(2*d)) ≤ (∑' j : ℕ, pairedColumnTerm c N S v j) ∧ (∑' j : ℕ, pairedColumnTerm c N S v j) ≤ (1+η)*H/(Real.pi^2*(N:ℝ)*(1-B/(N:ℝ))^(2*d))."))),
                DescribeRole.Theorem))));
}
