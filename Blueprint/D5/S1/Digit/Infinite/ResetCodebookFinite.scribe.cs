using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class ResetCodebookFiniteDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/Infinite/ResetCodebookFinite.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reset codebooks, actual sources and weighted lower-memory graphs.",
        H("Reset codebook: Finite"),
        Blocks(
            Node("common_memory_cutoff", "common_memory_cutoff", "common memory cutoff", "For the specified parameters, the following hypotheses imply the stated relation: (K : ℕ) (height eps : ℝ) (hh : 0 < height) (heps : 0 < eps) : ∃ n : ℕ, K ≤ n ∧ height*rho^n < eps", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("step", "step", "step", "The mathematical data are specified by step(low : Bool) (D : ℝ) := A low+rho*D.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("run", "run", "run", "The mathematical data are specified by run(low : Bool) (a : Return) (D : ℝ) := .", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("parameters", "parameters", "parameters", "For the specified parameters, the following hypotheses imply the stated relation: (low : Bool) : 0 < rho ∧ rho < 1 ∧ 0 < chi ∧ chi < 1 ∧ 0 < h low ∧ h low < E low ∧ E low ≤ 1/4", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("execute", "execute", "execute", "The mathematical data are specified by execute(low : Bool) (as : List Return) (D : ℝ) := as.foldl (fun x a => run low a x) D.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("run_bounds", "run_bounds", "run bounds", "For the specified parameters, the following hypotheses imply the stated relation: (low : Bool) (a : Return) (D : ℝ) (hD : 0 ≤ D) (hh : D ≤ h low) : 0 ≤ run low a D ∧ run low a D ≤ h low", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("execute_bounds", "execute_bounds", "execute bounds", "For the specified parameters, the following hypotheses imply the stated relation: (low : Bool) (as : List Return) (D : ℝ) (hD : 0 ≤ D) (hh : D ≤ h low) : 0 ≤ execute low as D ∧ execute low as D ≤ h low", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("initial", "initial", "initial", "The mathematical data are specified by initial(low anchor : Bool) := if anchor then Y low else X low.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("closedRun", "closedRun", "closedRun", "The mathematical data are specified by closedRun(low : Bool) (m r : ℕ) (D : ℝ) := h low-rho^m*(h low-chi^r*D).", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("run_closed", "run_closed", "run closed", "For the specified parameters, the following hypotheses imply the stated relation: (low : Bool) (a : Return) (D : ℝ) : run low a D=closedRun low a.val.1 a.val.2 D", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("reset_lifts", "reset_lifts", "reset lifts", "For the specified parameters, the following hypotheses imply the stated relation: (M : ℕ) (z : ℝ) (hz : A false ≤ z) : resetFloor M ≤ closedRun false M 1 z", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("execute_floor", "execute_floor", "execute floor", "For the specified parameters, the following hypotheses imply the stated relation: (low : Bool) (as : List Return) (D : ℝ) (hD : A low ≤ D) (hh : D ≤ h low) : A low ≤ execute low as D", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("weak_run", "weak_run", "weak run", "For the specified parameters, the following hypotheses imply the stated relation: (K : ℕ) (d : ℝ) (a : Return) (as : List Return) (D : ℝ) : Statement.weak K d (a::as) D ↔ a.val.2 ≤ K ∧ (a.val.2=K → d ≤ D) ∧ Statement.weak K d as (run false a D)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("weak_gain", "weak_gain", "weak gain", "For the specified parameters, the following hypotheses imply the stated relation: (K : ℕ) (d delta x y : ℝ) (as : List Return) (hd : 0 < delta) (hxy : x+delta ≤ y) (hw : Statement.weak K d as x) : Statement.weak K (d+delta*g^(totalWeight as)) as y", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("A_nonneg", "A_nonneg", "A nonneg", "For the specified parameters, the following hypotheses imply the stated relation: 0 ≤ A false", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("reset_actual_family", "reset_actual_family", "reset actual family", "For the specified parameters, the following hypotheses imply the stated relation: (anchor : Bool) (K M N : ℕ) (b d : ℝ) (hK : 2 ≤ K) (hM : 1 ≤ M) (hb : lambda-g^2*chi^K*h false < b) (hd : d=(lambda-b)/(g^2*chi^K)) (hreset : max (X false) (Y false) < Statement.B M) : 0 < Statement.actualEps anchor K M N b ∧ Statement.finiteActual anchor K M N b d hM", DescribeRole.Theorem, AssessedProvenance.FromRepo())
        )));

    private static DocumentBlock Node(string declaration, string identifier, string title, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("resetcodebookfinite-" + identifier.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), provenance,
            Blocks(Paragraph(Text(prose))), role);
}
