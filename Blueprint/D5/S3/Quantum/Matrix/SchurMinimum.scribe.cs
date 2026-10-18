using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class SchurMinimumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Schur quadratic form is the attained minimum over the internal block.",
        H("Attained Schur Minimum"),
        Blocks(Describe.Lean(
            DescribeId.Create("schur-quadratic-minimum"),
            DeclarationHandle.Create("D5/S3/Quantum/Matrix/SchurMinimum.schur_quadratic_is_least"),
            H("Boundary quadratic minimum"),
            StatementSource.FromAuthor(MinimumFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For a finite Hermitian block matrix with positive definite internal block C, "
                + "the set of energies at a fixed boundary vector has the stated least element. "
                + "It is attained at the negative inverse-block response. The proof applies "
                + "Mathlib's Schur decomposition and positive-semidefinite quadratic inequality. "
                + "This is a repository API wrapper of those upstream results."))),
            DescribeRole.Theorem),
            Paragraph(Text("Real quadratic energy and Gaussian free energy.")),
            Paragraph(Text(
                "Let x and z range over real Euclidean spaces of positive finite dimensions p and r, "
                + "with their standard Lebesgue volumes. Suppose the symmetric block matrix "
                + "L = [A B; Bᵀ C] is positive definite, and set "
                + "U(x,z) = xᵀAx/2 + xᵀBz + zᵀCz/2 and S = A − BC⁻¹Bᵀ. "
                + "The principal block C is positive definite. Testing the full quadratic form on "
                + "(x, −C⁻¹Bᵀx) also gives strict positive definiteness of S.")),
            Paragraph(Text(
                "The real specialization of Matrix.schur_complement_eq₂₂ gives "
                + "U(x,z) = xᵀSx/2 + vᵀCv/2, where v = z + C⁻¹Bᵀx. "
                + "Consequently, over all real hidden vectors z the minimum is attained uniquely "
                + "at z = −C⁻¹Bᵀx, and its value is xᵀSx/2. This includes x = 0, "
                + "arbitrary rectangular B, and noncommuting square blocks.")),
            Paragraph(Text(
                "For every real temperature τ > 0 the actual Lebesgue integrand exp(−U(x,z)/τ) "
                + "is integrable, and its integral over the entire hidden space is "
                + "exp(−xᵀSx/(2τ)) (2πτ)^(r/2) (det C)^(−1/2). "
                + "Both exponents are real numbers. To obtain the normalization, use the positive "
                + "matrix square root D of the same C: the standard Euclidean squared norm of Dv "
                + "is vᵀCv and det D = sqrt(det C) > 0. "
                + "Measure.map_linearMap_addHaar_eq_smul_addHaar supplies the actual volume factor "
                + "1/sqrt(det C), and GaussianFourier.integral_rexp_neg_mul_sq_norm supplies the "
                + "radial Gaussian integral. Translation invariance removes the hidden shift.")),
            Paragraph(Text(
                "Taking the real logarithm of this positive integral gives exactly "
                + "−τ log ∫ exp(−U(x,z)/τ) dz = xᵀSx/2 + (τ/2) log det C "
                + "− (rτ/2) log(2πτ). Thus the minimum of the actual energy and the free energy "
                + "of the actual integral are both differentiable in x, with Euclidean gradient Sx; "
                + "their derivative sends h to the Euclidean inner product of Sx and h. "
                + "This follows from the derivative of the inner product, symmetry of S, "
                + "and the displayed equality of functions.")),
            Paragraph(Text(
                "Here C is fixed independently of x. If the hidden stiffness varies with x, "
                + "the logarithmic determinant correction generally has a nonzero derivative. "
                + "Positive definiteness and τ > 0 are required for this full-space normalization; "
                + "a singular hidden block or a replacement measure does not have the stated meaning.")))));

    private static Formula MinimumFormula()
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula a = F.Id("A");
        Formula b = F.Id("B");
        Formula c = F.Id("C");
        Formula adjointB = Seq(b, Caret, Grp(Star));
        Formula schur = Seq(Open, a, Minus, b,
            Seq(c, Caret, Grp(Minus, D(1))), adjointB, Close);
        Formula pair = Seq(Begin, Grp(F.Id("pmatrix")), x, RowBreak, y,
            End, Grp(F.Id("pmatrix")));
        Formula block = Seq(Begin, Grp(F.Id("pmatrix")), a, Amp, b, RowBreak,
            adjointB, Amp, c, End, Grp(F.Id("pmatrix")));
        Formula energy = Seq(pair, Caret, Grp(Star), block, pair);
        Formula minimum = Seq(x, Caret, Grp(Star), schur, x);
        return Disp(Seq(Operatorname, Grp(F.Id("IsLeast")), Open,
            OpenBrace, energy, Sp, Mid, Sp, y, Sp, InMacro, Sp,
            Seq(Mathbb, Grp(F.Id("C")), Caret, Grp(F.Id("n"))),
            CloseBrace, Comma, Sp, minimum, Close));
    }
}
