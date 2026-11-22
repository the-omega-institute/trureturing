using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.FixedC2;

internal sealed class ActualFixedC2NeutralMonomialsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralMonomials.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fixed quotient product reduces neutral words by oscillator length.",
        H("Neutral Word Reduction in the Fixed Lattice C2 Quotient"),
        Blocks(
            Paragraph(Text("The lattice data consist of a natural-number rank and a symmetric integral Gram "
                + "matrix with even diagonal. The actual complex carrier consists of finitely supported "
                + "charge families of oscillator polynomials.")),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-fixed-product-ideal"),
                DeclarationHandle.Create(Prefix + "fixed_product_mem_c2"),
                H("The fixed minus-one mode preserves the fixed C2 span"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Commuting the (-1)-mode past a generator's (-2)-mode gives a finite "
                    + "sum of products at indices -3-j with j nonnegative. Translation puts all fixed "
                    + "products at indices at most -2 in the fixed C2 span. Induction on the span gives "
                    + "preservation in the second argument. The vacuum commutator gives commutativity "
                    + "modulo that span, hence preservation in the first argument as well."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-quotient-product"),
                DeclarationHandle.Create(Prefix + "fixedQuotientProduct"),
                H("Multiplication descends from the actual minus-one mode"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The intrinsic fixed quotient has a complex bilinear product. "
                    + "On two fixed representatives it takes the class of their actual (-1)-product. "
                    + "Preservation of the fixed C2 span in both arguments makes this independent "
                    + "of representatives."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-quadratic-word-length"),
                DeclarationHandle.Create(Prefix + "quadratic_word_length"),
                H("The leading word and the contraction terms"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual quadratic (-1)-product on a neutral word is a sum "
                    + "of two finitely supported mode expansions. The initial term of the first sum "
                    + "creates both oscillators and gives concatenation. Every other term uses one "
                    + "annihilation followed by one creation and lies in the span of words of the "
                    + "input length. Thus the difference from the concatenated word lies in the complex "
                    + "span of charge-zero words of exactly the input length, for any input word. "
                    + "On the empty word, vacuum creation gives the pair exactly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-fixed-quadratic-word-length"),
                DeclarationHandle.Create(Prefix + "fixed_quadratic_word_length"),
                H("The length reduction descends to the fixed quotient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An even neutral word is fixed by the sign involution. The quotient "
                    + "product of a pair class with such a word class differs from the concatenated class "
                    + "by a linear combination of neutral classes with two fewer oscillators than the "
                    + "concatenation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-neutral-word-high-pair"),
                DeclarationHandle.Create(Prefix + "neutral_word_high_pair"),
                H("A high pair shortens an even neutral word"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let the even neutral word be a permutation of a chosen pair "
                    + "followed by an even-length remainder. Assume the pair has total index at least seven "
                    + "and its first basis entry has nonzero Gram diagonal. Commutativity of the oscillator "
                    + "polynomials moves the chosen pair to the front. Its class vanishes, so the whole word "
                    + "class lies in the complex span of neutral classes of exactly the remainder's length."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-leech-neutral-word-high-pair"),
                DeclarationHandle.Create(Prefix + "leech_neutral_word_high_pair"),
                H("The high-pair reduction for the actual Leech lattice"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the actual Leech lattice, positive definiteness of the real Gram "
                    + "matrix gives the nonzero diagonal entry. If an even neutral word is a permutation "
                    + "of a pair of total index at least seven followed by an even-length remainder, its "
                    + "class lies in the complex span of neutral classes of exactly the remainder's length."))),
                DescribeRole.Theorem))));
}
