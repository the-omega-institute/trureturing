using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class ResetCodebookOrderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/Infinite/ResetCodebookOrder.";
    private static readonly BibKey Source = BibKey.Create("mathlib2026gelfandandivt");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reset codebooks, actual sources and weighted lower-memory graphs.",
        H("Reset codebook: Order"),
        Blocks(
            Node("complexify", "complexify", "The mathematical data are specified by complexify(A : Matrix ι ι ℝ) : Matrix ι ι ℂ := Complex.ofRealHom.mapMatrix A.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("radius", "radius", "The mathematical data are specified by radius(A : Matrix ι ι ℝ) : ℝ := (spectralRadius ℂ (complexify A)).toReal.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("radius_finite", "radius finite", "For the specified parameters, the following hypotheses imply the stated relation: (A : Matrix ι ι ℝ) : spectralRadius ℂ (complexify A) ≠ ∞", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("gelfand", "gelfand", "The nth root of the norm of the nth power of a finite complex matrix tends to its spectral radius. This is the classical Gelfand formula, applied to the complexification of a real matrix.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("positive_pow", "positive pow", "For the specified parameters, the following hypotheses imply the stated relation: (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) : ∀ i j, 0 ≤ (A^k) i j", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("positive_pow_le", "positive pow le", "For the specified parameters, the following hypotheses imply the stated relation: (A B : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j) (hAB : ∀ i j, A i j ≤ B i j) (k : ℕ) : ∀ i j, (A^k) i j ≤ (B^k) i j", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("positive_norm_le", "positive norm le", "For the specified parameters, the following hypotheses imply the stated relation: (A B : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j) (hAB : ∀ i j, A i j ≤ B i j) : ‖complexify A‖ ≤ ‖complexify B‖", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("radius_mono", "radius mono", "For finite square real matrices A and B, entrywise nonnegativity of A and the entrywise inequality A <= B imply that the complex spectral radius of A is at most that of B. The matrices need not be symmetric or irreducible. Entrywise comparisons of all powers and their row norms are combined with the Gelfand formula.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("t_linear", "t linear", "For the specified parameters, the following hypotheses imply the stated relation: t=(1+g)/2", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lambda_linear", "lambda linear", "For the specified parameters, the following hypotheses imply the stated relation: lambda=(1-g)/20", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("g_tight", "g tight", "For the specified parameters, the following hypotheses imply the stated relation: 236067/1000000 < g ∧ g < 236068/1000000", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("U_scalar_0", "U scalar 0", "For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (U.drop 0) x = ((-257/5 : ℝ) + (1096/5 : ℝ)*g) + (-g)^6*(x-c0)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("U_scalar_1", "U scalar 1", "For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (U.drop 1) x = ((-121/10 : ℝ) + (519/10 : ℝ)*g) + (-g)^5*(x-c0)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("U_scalar_2", "U scalar 2", "For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (U.drop 2) x = ((-7/2 : ℝ) + (121/10 : ℝ)*g) + (-g)^4*(x-c0)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("U_scalar_3", "U scalar 3", "For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (U.drop 3) x = ((-3/5 : ℝ) + (3 : ℝ)*g) + (-g)^3*(x-c0)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("U_scalar_4", "U scalar 4", "For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (U.drop 4) x = ((-3/5 : ℝ) + (3/5 : ℝ)*g) + (-g)^2*(x-c0)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("U_scalar_5", "U scalar 5", "For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (U.drop 5) x = ((-7/10 : ℝ) + (1/10 : ℝ)*g) + (-g)^1*(x-c0)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("V_scalar_0", "V scalar 0", "For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (V.drop 0) x = ((-342/5 : ℝ) + (1451/5 : ℝ)*g) + (-g)^6*(x-c0)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("V_scalar_1", "V scalar 1", "For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (V.drop 1) x = ((-83/5 : ℝ) + (342/5 : ℝ)*g) + (-g)^5*(x-c0)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("V_scalar_2", "V scalar 2", "For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (V.drop 2) x = ((-9/2 : ℝ) + (161/10 : ℝ)*g) + (-g)^4*(x-c0)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("V_scalar_3", "V scalar 3", "For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (V.drop 3) x = ((-3/5 : ℝ) + (4 : ℝ)*g) + (-g)^3*(x-c0)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("V_scalar_4", "V scalar 4", "For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (V.drop 4) x = ((-1/10 : ℝ) + (11/10 : ℝ)*g) + (-g)^2*(x-c0)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("V_scalar_5", "V scalar 5", "For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (V.drop 5) x = ((-7/10 : ℝ) + (1/10 : ℝ)*g) + (-g)^1*(x-c0)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("C_scalar_0", "C scalar 0", "For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 0) x = ((1/5 : ℝ) + (1/5 : ℝ)*g) + (-g)^20*(x-c0)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("C_scalar_1", "C scalar 1", "For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 1) x = ((1/2 : ℝ) + (3/10 : ℝ)*g) + (-g)^19*(x-c0)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("C_scalar_2", "C scalar 2", "For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 2) x = ((-4/5 : ℝ) + (0 : ℝ)*g) + (-g)^18*(x-c0)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("C_scalar_3", "C scalar 3", "For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 3) x = ((7/10 : ℝ) + (3/10 : ℝ)*g) + (-g)^17*(x-c0)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("C_scalar_4", "C scalar 4", "For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 4) x = ((9/10 : ℝ) + (3/10 : ℝ)*g) + (-g)^16*(x-c0)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("C_scalar_5", "C scalar 5", "For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 5) x = ((1/10 : ℝ) + (1/10 : ℝ)*g) + (-g)^15*(x-c0)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("C_scalar_6", "C scalar 6", "For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 6) x = ((-1/2 : ℝ) + (-1/10 : ℝ)*g) + (-g)^14*(x-c0)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("C_scalar_7", "C scalar 7", "For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 7) x = ((-2/5 : ℝ) + (0 : ℝ)*g) + (-g)^13*(x-c0)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("C_scalar_8", "C scalar 8", "For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 8) x = ((-9/10 : ℝ) + (-1/10 : ℝ)*g) + (-g)^12*(x-c0)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("C_scalar_9", "C scalar 9", "For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 9) x = ((6/5 : ℝ) + (2/5 : ℝ)*g) + (-g)^11*(x-c0)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("C_scalar_10", "C scalar 10", "For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 10) x = ((3/10 : ℝ) + (3/10 : ℝ)*g) + (-g)^10*(x-c0)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("C_scalar_11", "C scalar 11", "For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 11) x = ((0 : ℝ) + (1/5 : ℝ)*g) + (-g)^9*(x-c0)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("C_scalar_12", "C scalar 12", "For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 12) x = ((-1/5 : ℝ) + (0 : ℝ)*g) + (-g)^8*(x-c0)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("C_scalar_13", "C scalar 13", "For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 13) x = ((4/5 : ℝ) + (1/5 : ℝ)*g) + (-g)^7*(x-c0)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("C_scalar_14", "C scalar 14", "For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 14) x = ((3/5 : ℝ) + (1/5 : ℝ)*g) + (-g)^6*(x-c0)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("C_scalar_15", "C scalar 15", "For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 15) x = ((7/5 : ℝ) + (2/5 : ℝ)*g) + (-g)^5*(x-c0)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("C_scalar_16", "C scalar 16", "For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 16) x = ((-1/2 : ℝ) + (1/10 : ℝ)*g) + (-g)^4*(x-c0)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("C_scalar_17", "C scalar 17", "For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 17) x = ((-3/5 : ℝ) + (0 : ℝ)*g) + (-g)^3*(x-c0)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("C_scalar_18", "C scalar 18", "For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 18) x = ((-1/10 : ℝ) + (1/10 : ℝ)*g) + (-g)^2*(x-c0)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("C_scalar_19", "C scalar 19", "For the specified parameters, the following hypotheses imply the stated relation: (x : ℝ) : wordScalar (C.drop 19) x = ((3/10 : ℝ) + (1/10 : ℝ)*g) + (-g)^1*(x-c0)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("U_map", "U map", "For the specified parameters, the following hypotheses imply the stated relation: (D : ℝ) : wordScalar U (coord false D)=coord false (A false+rho*D)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("V_map", "V map", "For the specified parameters, the following hypotheses imply the stated relation: (D : ℝ) : wordScalar V (coord true D)=coord true (A true+rho*D)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("C_map", "C map", "For the specified parameters, the following hypotheses imply the stated relation: (low : Bool) (D : ℝ) : wordScalar C (coord low D)=coord low (chi*D)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("actual_errors", "actual errors", "For the specified parameters, the following hypotheses imply the stated relation: (w : List Label) (r : List (Fin 6)) (x tail : LegalDigits) (hp : addressPrefix w x tail) (hlen : w.length=r.length) (b eps : ℝ) (heps : 0<eps) (hb : 0<b-eps) (hc : wordCost w r (kappa tail)≤b-2*eps) (Q : ℝ→Fin 6) (hQ : ∀ i y, y∈Set.Ioo (cellLower i) (cellUpper i) → Q y=i) : ∃ errors : List ℝ, errors.length=r.length ∧ ∀ p : Fin r.length, |(errors[p.val]?.getD 0)|<b-eps ∧ Q (min (1+t) (max (-1) (kappa (originalT^[p.val] x)+(errors[p.val]?.getD 0))))=r[p.val]", DescribeRole.Theorem, AssessedProvenance.FromRepo())
        )));

    private static DocumentBlock Node(string declaration, string title, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("resetcodebookorder-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), provenance,
            Blocks(Paragraph(Text(prose))), role);
}
