using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.FixedC2;

internal sealed class ActualFixedC2NeutralPairsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralPairs.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Translation and fixed quadratic modes bound the surviving neutral two-oscillator classes.",
        H("Two-Oscillator Reduction in the Fixed Lattice C2 Quotient"),
        Blocks(
            Paragraph(Text("The lattice data consist of a natural-number rank and a symmetric integral Gram "
                + "matrix with even diagonal. The actual complex carrier consists of finitely supported "
                + "charge families of oscillator polynomials.")),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-neutral-pair"),
                DeclarationHandle.Create(Prefix + "neutralPair"),
                H("Neutral oscillator pairs"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The charge-zero state with polynomial X(i,a) X(j,b) is fixed by "
                    + "the sign involution. The oscillator indices start at zero, so X(i,a) represents "
                    + "the current mode numbered -a-1. Write pairClass for the image of this state in "
                    + "the intrinsic fixed C2 quotient."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-pair-normalize"),
                DeclarationHandle.Create(Prefix + "pair_class_normalize"),
                H("Translation moves the indices to one oscillator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Translation of a fixed state is its (-2)-product with the vacuum. "
                    + "Translating a pair therefore gives a zero class, with the two terms of the "
                    + "Leibniz rule weighted by a+1 and b+1. Iterating this relation expresses the class "
                    + "at (a,b) as (-1)^a times the binomial coefficient choosing a from a+b times "
                    + "the class at (0,a+b)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-odd-diagonal-pair"),
                DeclarationHandle.Create(Prefix + "diagonal_pair_class_odd"),
                H("Same-basis pairs vanish at odd total index"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When the two basis indices are equal and a+b is odd, the pair "
                    + "class is zero. Exchanging the two oscillators and using the translation relation "
                    + "identifies the normalized class with its negative."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-quadratic-cancellation"),
                DeclarationHandle.Create(Prefix + "fixed_quadratic_cancellation"),
                H("Cancellation of the four-oscillator terms"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Take twice the (-2)-product of X(i,0)^2 with X(i,2) X(j,b) and "
                    + "subtract the (-2)-product of X(i,1)^2 with X(i,0) X(j,b). Both products are "
                    + "intrinsic C2 generators. The four-oscillator terms cancel in the mode expansion. "
                    + "The resulting relation in the quotient is the sum of three classes, equal to zero. "
                    + "The (i,j) pair at (5,b) has coefficient 32 G(i,i). The (i,i) pair at (0,b+5) has "
                    + "coefficient 4 G(j,i) binom(-b-1,2)(b+5), with the generalized binomial coefficient. "
                    + "The (i,i) pair at (2,b+3) has coefficient 4(b+1) G(i,j)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-diagonal-high-pair"),
                DeclarationHandle.Create(Prefix + "diagonal_pair_class_high"),
                H("High pairs with equal basis indices vanish"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When j=i, normalization puts every term of the cancellation "
                    + "relation on the same class of total index n+5. Its combined coefficient is "
                    + "-(4/15) G(i,i) (n+5)(n+1)(n+3)(n+7)(n-1). For n at least two and G(i,i) nonzero, "
                    + "this forces the class to vanish."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-neutral-high-pair"),
                DeclarationHandle.Create(Prefix + "neutral_pair_class_high"),
                H("All neutral pair classes of total index at least seven vanish"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary j, the same-basis terms in the cancellation relation "
                    + "already vanish at total index at least seven. The remaining coefficient is "
                    + "nonzero after normalization when G(i,i) is nonzero. Thus every pair reduces to "
                    + "a multiple of one of the normalized pairs of total index zero through six, or to zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-gram-diagonal-ne"),
                DeclarationHandle.Create(Prefix + "gram_diagonal_ne"),
                H("A positive-definite Gram matrix has nonzero diagonal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If the real cast of the Gram matrix is positive definite, every Gram "
                    + "diagonal entry is nonzero. Testing the positive quadratic form on the corresponding "
                    + "coordinate vector gives strict positivity of the real cast of that entry."))),
                DescribeRole.Theorem))));
}
