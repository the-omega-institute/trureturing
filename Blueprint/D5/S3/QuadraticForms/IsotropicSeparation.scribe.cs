using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class IsotropicSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Null vectors detect every nonzero linear functional on a nondegenerate symmetric space over an algebraically closed field.",
        H("Null-Vector Separation"),
        Blocks(Describe.Lean(
            DescribeId.Create("null-vector-separation"),
            DeclarationHandle.Create("D5/S3/QuadraticForms/IsotropicSeparation.exists_null_detected_by_linear_form"),
            H("A null vector outside each functional kernel"),
            StatementSource.FromAuthor(Disp(Seq(
                Forall, Sp, F.Id("K"), Comma, Sp, F.Id("V"), Comma, Sp, F.Id("B"), Comma, Sp, F.Id("f"), Comma, Sp,
                Call("Field", F.Id("K")), Sp, Land, Sp,
                Call("CharZero", F.Id("K")), Sp, Land, Sp,
                Call("IsAlgClosed", F.Id("K")), Sp, Land, Sp,
                Call("FiniteDimensional", F.Id("K"), F.Id("V")), Sp, Land, Sp,
                Call("IsSymm", F.Id("B")), Sp, Land, Sp,
                Call("SeparatingLeft", F.Id("B")), Sp, Land, Sp,
                Num(2), Sp, Leq, Sp, Call("finrank", F.Id("K"), F.Id("V")), Sp, Land, Sp,
                F.Id("f"), Sp, Neq, Sp, Num(0), Sp, Rightarrow, Sp,
                Exists, Sp, F.Id("n"), Comma, Sp,
                Call("B", F.Id("n"), F.Id("n")), Sp, Eq, Sp, Num(0), Sp, Land, Sp,
                Call("f", F.Id("n")), Sp, Neq, Sp, Num(0)))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let K be an algebraically closed field of characteristic zero, V a finite-dimensional additive K-module of dimension at least two, and B a symmetric left-separating bilinear form on V. For every nonzero K-linear functional f there is a vector n with B(n,n)=0 and f(n) nonzero. In particular the constructed vector is nonzero. No positive-definiteness, real signature, inner product or unitary structure is assumed.")),
                Paragraph(Text("Mathlib's orthogonal-basis theorem supplies an orthogonal basis. Left separation makes each diagonal basis pairing nonzero. Choose a basis vector detected by f and a distinct second basis vector. Algebraic closedness supplies a square root of the negative ratio of their diagonal pairings. The sum and difference of the first basis vector with the scaled second basis vector are both null; if f killed both, their sum would force f to kill the first basis vector. Every division uses the proved nonzero second diagonal pairing, and characteristic zero makes two invertible.")),
                Paragraph(Text("This is a reusable algebraic separation construction, not a new orthogonal-basis or algebraic-closedness theorem. It directly reuses LinearMap.BilinForm.exists_orthogonal_basis, LinearMap.IsOrthoᵢ.not_isOrtho_basis_self_of_separatingLeft and IsAlgClosed.exists_eq_mul_self. No claim of literature originality is made.")),
                Paragraph(Text("For the original complexified integral lattice, apply the theorem to Matrix.toBilin' of gramComplex and the functional v maps to gramPair(v,complexCharge(beta)). The definition complexCharge(beta)(i) is the integer coefficient beta(i) cast to the complex numbers, so injectivity of this cast proves that nonzero beta has nonzero complexCharge. An explicit inverse Gram equation supplies nondegeneracy; the physical original-Q interface continues to require both Gram inverse equations and rank twenty-six. The conclusion supplies exactly a nullDirection with chosenP nonzero, not a real or positive physical frame.")),
                Paragraph(Text("The existing adaptedPartner_relations then gives its literal null partner, unit pairing and original charge decomposition. Completing a frame requires a basis of the hyperbolic plane's orthogonal complement, both literal matrix inverse equations, the exact null/adaptedPartner rows, and all-row xDual and yDual equations. This theorem alone proves none of those frame equations, Q squared zero, no-ghost, string dynamics or AdS/CFT. The zero-charge exceptional sector and the full original physical objective remain open."))),
            DescribeRole.Theorem))));
}
