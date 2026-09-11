using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class CommutantSemisimpleDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/CommutantSemisimple.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite-dimensional unitary group action has a semisimple commutant. "
            + "An integer shear action has a nonzero Jacobson radical, showing why "
            + "the unitary hypothesis matters.",
        H("Semisimple Unitary Commutants"),
        Blocks(
            Paragraph(Text(
                "The group is arbitrary: neither finiteness nor compactness is required. "
                    + "The matrices have a finite index type and complex entries. "
                    + "The commutant is the complex subalgebra of matrices commuting with "
                    + "every matrix in the supplied representation.")),
            Result("adjoint-radical", "jacobson_eq_bot_of_conjTranspose_closed",
                "Adjoint closure forces a zero radical",
                "Let A be a unital complex matrix subalgebra closed under conjugate transpose. "
                    + "It is finite dimensional, so its Jacobson radical is a nilpotent ideal. "
                    + "For X in that radical, the product of the adjoint of X with X is again "
                    + "in the radical. Its trace is zero by nilpotence. The positive trace "
                    + "pairing then forces X to be zero."),
            Result("commutant-adjoint", "commutant_conjTranspose_mem_of_unitary",
                "Unitary commutants are closed under adjoints",
                "The adjoint of the matrix representing g is the matrix representing its "
                    + "inverse. Thus the image of the representation is closed under adjoints, "
                    + "and so is its centralizer."),
            Result("semisimple", "commutant_isSemisimpleRing_of_unitary",
                "Unitarity implies semisimplicity",
                "Apply the zero-radical theorem to the commutant. An Artinian ring with "
                    + "zero Jacobson radical is semisimple. No group average or integral "
                    + "is involved."),
            Result("record-capacity", "unitary_commutant_has_record_capacity",
                "One block-size bound for every equivariant record resolution",
                "The semisimple complex commutant admits a product decomposition into full "
                    + "matrix algebras with nonzero block sizes. The sum of those sizes bounds "
                    + "every finite family of nonzero equivariant orthogonal idempotents "
                    + "summing to identity. Semisimplicity follows from unitarity here."),
            Result("shear-centralizer", "unipotent_commutant_characterization",
                "The integer shear commutant",
                "The integer z acts by the matrix with rows (1,z) and (0,1). "
                    + "An arbitrary complex two-by-two matrix commutes with every such shear "
                    + "exactly when it has rows (a,b) and (0,a), for complex a and b."),
            Result("shear-radical", "unipotent_radical_element_mem",
                "The upper-right matrix unit belongs to the radical",
                "Let E have upper-right entry one and all other entries zero. For every "
                    + "element Y of the shear commutant, one minus Y times E is a left inverse "
                    + "of one plus Y times E. The Jacobson membership criterion puts E in "
                    + "the radical."),
            Result("shear-nonzero", "unipotent_radical_element_ne_zero",
                "The radical element is nonzero",
                "The upper-right entry of E is one. Its inclusion in the commutant is "
                    + "injective, so E is nonzero as an element of that algebra."),
            Result("shear-not-semisimple", "unipotent_commutant_not_isSemisimpleRing",
                "The shear commutant is not semisimple",
                "A semisimple ring has zero Jacobson radical. The shear commutant contains "
                    + "the nonzero radical element E, so it is not semisimple. This integer "
                    + "representation disproves the claim obtained by omitting unitarity."),
            Result("unitarity-needed", "not_all_integer_matrix_commutants_semisimple",
                "Universal semisimplicity without unitarity is false",
                "The claim that every complex two-dimensional integer representation has "
                    + "a semisimple commutant is false: apply it to the shear representation "
                    + "and its nonzero radical gives a contradiction."))));

    private static DocumentBlock Result(string id, string declaration, string title, string text) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + declaration), H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/Quantum/mathlib2026commutantradical")),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
