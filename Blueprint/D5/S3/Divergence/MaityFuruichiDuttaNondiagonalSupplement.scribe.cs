using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Divergence;

internal sealed class MaityFuruichiDuttaNondiagonalSupplementDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common orthogonal change of basis makes both states nondiagonal while preserving the Tsallis ordering reversal.",
        H("Both states nondiagonal in the same basis"),
        Blocks(
            Paragraph(Text("This supplement answers Supriyo Dutta's question of 3 November 2026. "
                + "The mathematical note is by Haobo Ma and Wenlin Zhang, licensed CC BY 4.0. "
                + "It supplements the existing Maity-Furuichi-Dutta ordering refutation and does not resolve another conjecture. "
                + "Supriyo Dutta is distinct from Soumyojyoti Dutta and Tushar in other correspondence.")),
            Entry("orthogonal-matrix", "U", "The common change of basis",
                "U = (1/sqrt(2)) [[1,1],[1,-1]] is real, self-adjoint and orthogonal.", DescribeRole.Definition),
            Entry("first-state", "rhohat", "The first nondiagonal state",
                "rhohat = (1/10) [[5,3],[3,5]]. Both off-diagonal entries are 3/10.", DescribeRole.Definition),
            Entry("second-state", "sigmahat", "The second nondiagonal state",
                "sigmahat = (1/250) [[125+12 sqrt(6),-69],[-69,125-12 sqrt(6)]]. "
                + "Both off-diagonal entries are -69/250.", DescribeRole.Definition),
            Entry("invariance", "functions_unitary", "The three actual source functions are unitarily invariant",
                "The same unitary conjugates both arguments. Every real spectral function commutes with "
                + "this conjugation, and cyclicity preserves its trace. Consequently the existing renyiRZ, B2 "
                + "and tsallis definitions retain their values, for all parameters. On positive definite "
                + "states these functions use positive spectral calculus. The extension to arbitrary matrices "
                + "in the statement follows the total cfc convention, which is zero outside its predicate."),
            Entry("states", "matrix_facts", "Density, determinants, entries and noncommutation",
                "Both matrices are positive definite with trace one and determinant 4/25. The (0,1) entry "
                + "of their commutator is -18 sqrt(6)/625, which is nonzero. Thus they are noncommuting "
                + "density matrices with nonzero off-diagonal entries in this common basis."),
            Entry("eigenvalues", "characteristic_polynomials", "The two eigenvalues",
                "Each characteristic polynomial is (X-4/5)(X-1/5), so each state has eigenvalues "
                + "4/5 and 1/5, each with multiplicity one."),
            Entry("common-basis", "common_orthogonal_conjugation", "One orthogonal matrix conjugates the entire pair",
                "The original states are rho = diag(4/5,1/5) and sigma = (1/125) [[28,6 sqrt(6)],[6 sqrt(6),97]]. "
                + "The displayed rhohat and sigmahat equal U rho U* and U sigma U*. Every real spectral "
                + "function is covariant, including the powers and deformed logarithm occurring in all three "
                + "source functions. The commutator is conjugated by that same U. Nondiagonality depends "
                + "on the common basis; the bound values and noncommutation are invariant."),
            Entry("parameters", "parameter_conditions", "The source parameters are admissible",
                "At alpha = r = 1/2, z = 2 and q = 1, all five source conditions hold: "
                + "0 <= alpha, alpha < 1, r is nonzero, z > 0 and q > 1-alpha."),
            Entry("spectral-quantities", "spectral_quantities", "The spectral sandwiches",
                "The fidelity trace F for the nondiagonal pair is exactly (2117+288 sqrt(2))/3125. "
                + "The inverse-power sandwich is U A U*, where A = (1/25) [[7,3 sqrt(6)],[3 sqrt(6),97]] "
                + "is the original inverse-power sandwich. These identities transport the actual spectral "
                + "expressions used by the bounds."),
            Entry("values", "exact_values_and_bounds", "Exact values and the strict chain",
                "The old exact sandwich trace (2117+288 sqrt(2))/3125 gives "
                + "B1 = renyiRZ = 4(1-sqrt((2117+288 sqrt(2))/3125)). The existing positive square-root "
                + "calculation gives B2 = 2-20/sqrt(154). Transport by the common U gives "
                + "B2 < 2/5 < B1. The two-point functional calculus also gives the new exact value "
                + "D = tsallis(1/2,rhohat,sigmahat) = 48/125. Since 1250^2 < 154*101^2, D < B2 < B1. "
                + "Thus both individual upper bounds hold at this pair while their proposed relative order fails."),
            Entry("restricted-order", "claim", "The old ordering restricted to this nondiagonal setting",
                "This is the already refuted comparison B1 <= B2, restricted to positive definite "
                + "noncommuting qubit states with trace one and nonzero (0,1) entries in the same basis, "
                + "at the displayed source parameters. It introduces no new conjecture.", DescribeRole.Definition),
            Entry("refutation", "result", "The same reversal persists with both states nondiagonal",
                "The explicit states meet every hypothesis of the restricted comparison, and their strict "
                + "bound reversal contradicts its conclusion. This says nothing about other parameter choices "
                + "or the source's commuting comparison."))));

    private static DocumentBlock Entry(string id, string name, string title, string prose,
        DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose)), Paragraph(Text("Complete Lean statement: " + Exact(name).Replace('\n', ' ').Replace('\r', ' ')))), role);
    private static string Exact(string name) => name switch
    {
        "U" => "def U : Matrix (Fin 2) (Fin 2) ℂ :=\n  (1 / Real.sqrt 2 : ℝ) • !![1, 1; 1, -1]",
        "rhohat" => "def rhohat : Matrix (Fin 2) (Fin 2) ℂ := !![1/2, 3/10; 3/10, 1/2]",
        "sigmahat" => "def sigmahat : Matrix (Fin 2) (Fin 2) ℂ :=\n  !![((125 + 12 * Real.sqrt 6) / 250 : ℝ), -69/250;\n      -69/250, ((125 - 12 * Real.sqrt 6) / 250 : ℝ)]",
        "functions_unitary" => "theorem functions_unitary {n : ℕ} (u : unitary (Matrix (Fin n) (Fin n) ℂ))\n    (ρ σ : Matrix (Fin n) (Fin n) ℂ) (α r z q : ℝ) :\n    let e := Unitary.conjStarAlgAut ℂ _ u\n    renyiRZ α r z (e ρ) (e σ) = renyiRZ α r z ρ σ ∧\n    B2 α q (e ρ) (e σ) = B2 α q ρ σ ∧\n    tsallis α (e ρ) (e σ) = tsallis α ρ σ",
        "matrix_facts" => "theorem matrix_facts :\n    rhohat.PosDef ∧ rhohat.trace = 1 ∧ sigmahat.PosDef ∧ sigmahat.trace = 1 ∧\n    rhohat.det = 4/25 ∧ sigmahat.det = 4/25 ∧\n    rhohat 0 1 = 3/10 ∧ rhohat 1 0 = 3/10 ∧\n    sigmahat 0 1 = -69/250 ∧ sigmahat 1 0 = -69/250 ∧\n    (rhohat * sigmahat - sigmahat * rhohat) 0 1 = (-18 * Real.sqrt 6 / 625 : ℝ) ∧\n    rhohat * sigmahat ≠ sigmahat * rhohat",
        "characteristic_polynomials" => "theorem characteristic_polynomials :\n    rhohat.charpoly = (Polynomial.X - Polynomial.C (4/5:ℂ)) * (Polynomial.X - Polynomial.C (1/5:ℂ)) ∧\n    sigmahat.charpoly = (Polynomial.X - Polynomial.C (4/5:ℂ)) * (Polynomial.X - Polynomial.C (1/5:ℂ))",
        "common_orthogonal_conjugation" => "theorem common_orthogonal_conjugation :\n    star U = U ∧ U * U = 1 ∧\n    rhohat = U * rho * star U ∧ sigmahat = U * sigma * star U ∧\n    (∀ (f : ℝ → ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ),\n      cfc f (U * X * star U) = U * cfc f X * star U) ∧\n    rhohat * sigmahat - sigmahat * rhohat = U * (rho * sigma - sigma * rho) * star U",
        "parameter_conditions" => "theorem parameter_conditions :\n    (0:ℝ) ≤ 1/2 ∧ (1/2:ℝ) < 1 ∧ (1/2:ℝ) ≠ 0 ∧ (0:ℝ) < 2 ∧ (1-(1/2:ℝ)) < 1",
        "spectral_quantities" => "theorem spectral_quantities :\n    (trace (cfc (fun x:ℝ => x^(2:ℝ))\n      (cfc (fun x:ℝ => x^(1/8:ℝ)) sigmahat *\n        cfc (fun x:ℝ => x^(1/4:ℝ)) rhohat *\n        cfc (fun x:ℝ => x^(1/8:ℝ)) sigmahat))).re =\n      (2117 + 288 * Real.sqrt 2) / 3125 ∧\n    cfc (fun x:ℝ => x^(-(1/2:ℝ))) rhohat * sigmahat *\n      cfc (fun x:ℝ => x^(-(1/2:ℝ))) rhohat = U * A * star U",
        "exact_values_and_bounds" => "theorem exact_values_and_bounds :\n    renyiRZ (1/2) (1/2) 2 rhohat sigmahat =\n      4 * (1 - Real.sqrt ((2117 + 288 * Real.sqrt 2) / 3125)) ∧\n    B2 (1/2) 1 rhohat sigmahat = 2 - 20 / Real.sqrt 154 ∧\n    tsallis (1/2) rhohat sigmahat = 48/125 ∧\n    B2 (1/2) 1 rhohat sigmahat < 2/5 ∧\n    (2/5:ℝ) < renyiRZ (1/2) (1/2) 2 rhohat sigmahat ∧\n    tsallis (1/2) rhohat sigmahat < B2 (1/2) 1 rhohat sigmahat ∧\n    B2 (1/2) 1 rhohat sigmahat < renyiRZ (1/2) (1/2) 2 rhohat sigmahat",
        "claim" => "def claim : Prop := ∀ ρ σ : Matrix (Fin 2) (Fin 2) ℂ,\n  ρ.PosDef → ρ.trace = 1 → σ.PosDef → σ.trace = 1 → ρ * σ ≠ σ * ρ →\n  ρ 0 1 ≠ 0 → σ 0 1 ≠ 0 →\n  renyiRZ (1/2) (1/2) 2 ρ σ ≤ B2 (1/2) 1 ρ σ",
        "result" => "theorem result : ¬ claim",
        _ => throw new ArgumentException("Unknown source declaration", nameof(name))
    };

}
