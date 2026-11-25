using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.Charge;

internal sealed class ChargeHermitianDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/Charge/ChargeHermitian.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical original charge averaging constructs positive invariant conjugate-first Hermitian geometry.",
        H("The Original Ground Charge-Averaged Hermitian Form"),
        Blocks(
            Paragraph(Text("For every original D, n and representation rho on Ground(n), define "
                + "H(x,y)=card(ModTwoCharge(D)) inverse times sum_v sum_t conjugate((A_v x)(t)) (A_v y)(t). "
                + "The t index is the entire finite function type Fin(n) to Z/2, not a sample or an occupation truncation. "
                + "The charge index is the entire original reduced charge type. Finite nonempty cardinality makes the "
                + "normalization positive, including n zero. This is a complex sesquilinear form, conjugate-linear in its first slot.")),
            Describe.Lean(
                DescribeId.Create("actual-positive-invariant-ground-geometry"),
                DeclarationHandle.Create(Prefix + "actual_charge_geometry"),
                H("Canonical Positive Geometry on the Original Carrier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The theorem constructs GroundHermitian for exactly this chargeForm, assuming only "
                        + "rho([(1,0)]) is the negative identity. It proves both additive slot laws, conjugate first-slot "
                        + "and linear second-slot scalar laws, Hermitian symmetry, zero imaginary diagonal, nonnegative "
                        + "real diagonal and strictly positive real diagonal for every nonzero state. Both left and right "
                        + "radicals vanish. The diagonal is the positive real normalization times the finite sum of "
                        + "Complex.normSq of all transformed coordinates. Mathlib supplies normSq nonnegativity and its "
                        + "strict positivity criterion. The exact A_0 identity summand retains any nonzero coordinate of x, "
                        + "so positivity is proved rather than postulated.")),
                    Paragraph(Text("For every original quotient element g, the original signed right-translation law "
                        + "permutes v to v+charge(g). Conjugate times ordinary scalar cancels the modulus-one original sign "
                        + "in each coordinate pairing. Finite translation reindexing proves H(rho(g)x,rho(g)y)=H(x,y). "
                        + "Applying this to x and rho(g inverse)y proves H(rho(g)x,y)=H(x,rho(g inverse)y). "
                        + "The inverse is the actual group inverse, not an unproved identification with charge reflection.")),
                    Paragraph(Text("Finite-group Hermitian averaging is classical and not claimed novel. No real-signature "
                        + "positivity, invariant inner product or unitarity is assumed. The form hypotheses do not require "
                        + "a rank-24 specialization or a determinant unit; the later full operator twirl does require "
                        + "the unit determinant and rank(D)=n+n. No invariant complex-bilinear or symmetric form, nor a "
                        + "Frobenius-Schur conclusion, follows from this Hermitian result. The full VOA/string/AdS objective remains open."))),
                DescribeRole.Theorem))));
}
