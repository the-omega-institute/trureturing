using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices;

internal sealed class ContractingIntegralSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer lattice orbits separate strict contractions from every native matrix power.",
        H("Contracting integral separation"),
        Blocks(Describe.Lean(
            DescribeId.Create("polynomial-power-separation"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Lattices/ContractingIntegralSeparation.polynomial_sub_pow_isUnit"),
            H("Every integral power is separated"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let the coordinate type be any finite type with decidable equality, "
                    + "let A be an integer square matrix, and let f be a rational polynomial. "
                    + "Evaluate f at A over the rationals to obtain F. If F is invertible "
                    + "and its scalar extension to the reals has Euclidean operator norm "
                    + "strictly below one, then F minus A to the k-th power is invertible "
                    + "over the rationals for every natural number k, including zero. "
                    + "The empty coordinate type is included. A need not be symmetric, "
                    + "have zero diagonal, or be invertible.")),
                Paragraph(Text(
                    "A vector in the kernel gives equal first iterates under F and A to "
                    + "the k-th power. Polynomial commutation makes all subsequent iterates "
                    + "equal. Clear the finitely many rational denominators to obtain an "
                    + "integer vector. Its integral matrix iterates remain integral, while "
                    + "the Euclidean norms of the equal F iterates tend to zero. An iterate "
                    + "of norm below one has every integer coordinate zero. Invertibility "
                    + "of F and the nonzero denominator then force the original vector zero.")),
                Paragraph(Text(
                    "For the same-material native law, the integral adjacency supplies A "
                    + "and the contracting target supplies f. This proves the law separation "
                    + "used in Lemma 78.2 of Native Leaf Boundary Acquisition II. It does "
                    + "not prove the adaptive execution fibre correspondence or the scalar "
                    + "Read lower bound of Theorem 78.3."))),
            DescribeRole.Theorem))));
}
