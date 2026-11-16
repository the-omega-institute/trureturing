using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Characters;

internal sealed class LatticeDiscriminantFusionAlgebraDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Characters/LatticeDiscriminantFusionAlgebra.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite pointed fusion algebra carried by the discriminant group.",
        H("Finite Discriminant Fusion Algebra"),
        Blocks(
            Definition("fusion-algebra", "FusionAlgebra", "Finite fusion algebra",
                "For an original positive even integral lattice D, FusionAlgebra D is the complex additive monoid algebra of the finite discriminant group. This is a finite algebraic package of the Weil S-kernel coefficients; it does not assert a tensor-category or vertex-operator-algebra construction."),
            Definition("basis", "basis", "Discriminant basis",
                "The basis vector indexed by a discriminant class is the monoid-algebra single at that class with coefficient 1."),
            Theorem("pointed-multiplication", "basis_mul", "Pointed multiplication",
                "Multiplication of basis vectors is indexed by addition in the discriminant group."),
            Theorem("basis-zero", "basis_zero", "Zero class is the unit",
                "The basis vector indexed by the zero discriminant class is the algebra unit."),
            Theorem("basis-commutative", "basis_mul_comm", "Commutative pointed multiplication",
                "The pointed basis multiplication is commutative."),
            Theorem("basis-associative", "basis_mul_assoc", "Associative pointed multiplication",
                "The pointed basis multiplication is associative."),
            Theorem("verlinde-structure-constants", "basis_mul_coeff_eq_fusionCoefficient", "Structure constants are finite Verlinde coefficients",
                "The coefficient of the basis class c in the product of the classes a and b is exactly the normalized finite Verlinde coefficient computed from the Weil S-kernel."),
            Definition("augmentation", "augmentation", "Augmentation",
                "The augmentation is the algebra homomorphism sending every discriminant basis element to 1."),
            Theorem("augmentation-basis", "augmentation_basis", "Augmentation on basis vectors",
                "The augmentation sends every discriminant basis vector to 1."))));

    private static DocumentBlock Theorem(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static DocumentBlock Definition(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
