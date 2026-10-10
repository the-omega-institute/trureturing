using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class ResetCodebookGrowthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/Infinite/ResetCodebookGrowth.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reset codebooks, actual sources and weighted lower-memory graphs.",
        H("Reset codebook: Growth"),
        Blocks(
            Node("radius_smul", "radius_smul", "radius smul", "For the specified parameters, the following hypotheses imply the stated relation: (A : Matrix ι ι ℝ) (c : ℝ) (hc : 0 ≤ c) : radius (c • A) = c * radius A", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("positive_row_le_norm", "positive_row_le_norm", "positive row le norm", "For the specified parameters, the following hypotheses imply the stated relation: (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j) (i : ι) : (∑ j, A i j) ≤ ‖complexify A‖", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("row_power_lower", "row_power_lower", "row power lower", "For the specified parameters, the following hypotheses imply the stated relation: (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j) (r : ℝ) (hr : 0 ≤ r) (hrow : ∀ i, r ≤ ∑ j, A i j) (k : ℕ) : ∀ i, r^k ≤ ∑ j, (A^k) i j", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("row_lower_radius", "row_lower_radius", "row lower radius", "If a finite nonempty nonnegative matrix has every row sum at least a nonnegative real r, its spectral radius is at least r. The same lower bound propagates to row sums of all powers before taking the Gelfand limit.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("radius_sq", "radius_sq", "radius sq", "For the specified parameters, the following hypotheses imply the stated relation: (A : Matrix ι ι ℝ) : radius (A^2) = radius A ^ 2", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("small_powers", "small_powers", "small powers", "For the specified parameters, the following hypotheses imply the stated relation: (n : ℕ) : 0 ≤ g^n ∧ g^n ≤ (1/4:ℝ)^n", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("auto_positive", "auto_positive", "auto positive", "For the specified parameters, the following hypotheses imply the stated relation: 0 < lambda-rho", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("U_cost", "U_cost", "U cost", "For the specified parameters, the following hypotheses imply the stated relation: (D : ℝ) (hD : 0 ≤ D) (hD1 : D ≤ 1/4) : wordCost U sixColor (coord false D) ≤ max (lambda-g^2*D) (lambda-rho)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("V_cost", "V_cost", "V cost", "For the specified parameters, the following hypotheses imply the stated relation: (D : ℝ) (hD : 0 ≤ D) (hD1 : D ≤ 1/4) : wordCost V sixColor (coord true D) ≤ max (lambda-g^2*D) (lambda-rho)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("C_cost", "C_cost", "C cost", "For the specified parameters, the following hypotheses imply the stated relation: (z : ℝ) (hz : |z-c0| ≤ 1/4) : wordCost C twentyColor z ≤ lambda-rho", DescribeRole.Theorem, AssessedProvenance.FromRepo())
        )));

    private static DocumentBlock Node(string declaration, string identifier, string title, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("resetcodebookgrowth-" + identifier.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), provenance,
            Blocks(Paragraph(Text(prose))), role);
}
