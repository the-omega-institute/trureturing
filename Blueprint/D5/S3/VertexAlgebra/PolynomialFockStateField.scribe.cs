using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class PolynomialFockStateFieldDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/PolynomialFockStateField.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997locality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every complex polynomial Fock state has a creative local field with actual translation.",
        H("Polynomial Fock State Fields"),
        Blocks(
            Paragraph(Text("Y extends the sorted monomial occurrence construction linearly "
                + "to every polynomial. Each occurrence of X_k contributes the kth divided "
                + "derivative of the actual current, with explicit right nesting ending "
                + "in the identity field. No degree cutoff or normal-product associativity "
                + "is assumed. Locality holds as an endomorphism identity with an order "
                + "depending only on the two polynomial states. These rank-one formal "
                + "fields do not assert an actual Monster realization or physical geometry.")),
            Describe.Lean(
                DescribeId.Create("polynomial-fock-state-field-creation"),
                DeclarationHandle.Create(Prefix + "stateField_creation"),
                H("Every polynomial is created and the quadratic conformal field is actual"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Y(1) is the identity field and Y(X_0) is the actual "
                    + "current. For every polynomial p, Y(p)_(−1) applied to the vacuum "
                    + "equals p, and every nonnegative mode kills the vacuum. For every "
                    + "integer n, the nth mode of Y((1/2)X_0^2) is the existing L(n−1). "
                    + "The comparison splits the actual finite Sugawara sum into its "
                    + "two integer-sign halves."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("polynomial-fock-state-field-translation"),
                DeclarationHandle.Create(Prefix + "stateField_translation"),
                H("The actual L(-1) translates every polynomial field"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("L(-1) kills the vacuum. For every polynomial p "
                    + "and every integer n, [L(-1),Y(p)_n]=-n Y(p)_(n−1) as an "
                    + "endomorphism of the same complex polynomial Fock space. The "
                    + "current commutator propagates through divided derivatives, "
                    + "the actual ordered products and the monomial basis. No premise "
                    + "postulates translation of the resulting Y."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("polynomial-fock-state-field-locality"),
                DeclarationHandle.Create(Prefix + "stateField_locality"),
                H("Every polynomial pair is operator-uniformly local"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every two polynomial states p and q there is "
                    + "a natural N such that the Nth binomial finite difference of "
                    + "[Y(p)_m,Y(q)_n] vanishes for every pair of integer mode indices "
                    + "as an endomorphism. N is selected from field words and the finite "
                    + "polynomial supports, before either index or input vector. The "
                    + "normal-product locality kernel is used by the actual Y."))),
                DescribeRole.Theorem))));
}
