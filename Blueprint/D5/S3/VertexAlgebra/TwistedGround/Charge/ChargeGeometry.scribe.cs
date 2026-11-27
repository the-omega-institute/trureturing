using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.Charge;

internal sealed class ChargeGeometryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/Charge/ChargeGeometry.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The canonical original charge section has exact signed translations and Gram conjugation characters.",
        H("Original Canonical Charge Geometry"),
        Blocks(
            Paragraph(Text("Keep the original even integral lattice D, lower-triangular cocycle, sign extension E, "
                + "reflection subgroup K and quotient E/K. The fixed integral section lifts each mod-two coordinate "
                + "to its value zero or one; A_v is rho([(0,integralLift(v))]) and D_v is the image of that group inverse. "
                + "The representation is any original complex representation on Ground(n) with the negative central sign. "
                + "No unitary structure, trace formula, irreducibility, positivity of the lattice or occupation cutoff is assumed.")),
            Describe.Lean(
                DescribeId.Create("original-projective-charge-translation"),
                DeclarationHandle.Create(Prefix + "charge_right_translation"),
                H("The Actual Right-Translation Cocycle"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every original quotient element g, let w be the charge coordinate of quotientEquiv(g) "
                        + "and let s be its sign coordinate. Original quotient multiplication gives "
                        + "A_v rho(g)=complexSign(s+modTwoCocycle(v,w)) A_(v+w). "
                        + "The map v to v+w is a permutation of the full finite mod-two charge type. "
                        + "The scalar is exactly the original sign character, whose conjugate times itself is one. "
                        + "There is no substitution of a convenient Weyl representation for rho."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-gram-character-cancellation"),
                DeclarationHandle.Create(Prefix + "gram_character_sum"),
                H("Exact Finite Character Cancellation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Conjugation of A_w by A_v and its actual inverse D_v multiplies A_w by "
                        + "complexSign(modTwoPairing(v,w)). The original reduced commutation identity supplies this exact sign. "
                        + "For a unit Gram determinant and w nonzero, nondegeneracy supplies a partner v with nonzero pairing; "
                        + "over Z/2 that value is one and its complex sign is negative one. The resulting AddChar is nontrivial. "
                        + "Mathlib AddChar.sum_eq_zero_of_ne_one is applied directly: its proof translates the finite sum by a "
                        + "nontrivial character witness using AddGroup.addLeft_bijective. Thus the sum is zero for every "
                        + "nonzero w, and is the full charge cardinality for w zero. No character orthogonality is assumed.")),
                    Paragraph(Text("These are classical projective representation and character-orthogonality constructions, "
                        + "not claimed as new mathematics. The substantive local bridge is to the exact original cocycle and "
                        + "canonical section, consumed in the positive Hermitian form and the all-End charge twirl. "
                        + "Rank zero has a sole zero charge and no nontrivial-character branch. This finite ground increment "
                        + "does not establish twisted Jacobi, fusion, orbifold extension, Monster symmetry, string theory or AdS/CFT."))),
                DescribeRole.Theorem))));
}
