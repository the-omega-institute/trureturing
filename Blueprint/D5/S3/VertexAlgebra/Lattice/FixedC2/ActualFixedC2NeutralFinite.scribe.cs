using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.FixedC2;

internal sealed class ActualFixedC2NeutralFiniteDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralFinite.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two reductions in word length give a finite spanning family for the fixed vacuum-charge image.",
        H("Finite Dimension of the Fixed Neutral Image"),
        Blocks(
            Paragraph(Text("LatticeData D consists of a natural-number rank and a symmetric integral Gram "
                + "matrix G with even diagonal. A word is a list of pairs (i,n), with i a basis index "
                + "and n a zero-based natural oscillator index. Total index is the sum of the n entries. "
                + "The cutoffs below use the actual rank-24 Golay-Leech lattice data.")),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-neutral-word-high-total-index"),
                DeclarationHandle.Create(Prefix + "leech_neutral_word_high_total_index"),
                H("An even word with total index at least seven shortens"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an even Leech word with total index at least seven, choose one "
                    + "letter to accumulate the indices of the others. Each transfer relates the two word "
                    + "classes by a nonzero signed binomial factor and terms with two fewer letters. The "
                    + "accumulated oscillator and another letter form a vanishing high pair. The original "
                    + "class lies in the complex span of strictly shorter even neutral words."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-neutral-word-product-length"),
                DeclarationHandle.Create(Prefix + "neutral_word_mul_append"),
                H("Concatenation is the leading term of the word product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any D and two even neutral words, their quotient product differs from "
                    + "concatenation by a span of words of strictly smaller length than the sum of "
                    + "their lengths. The shorter words are even and neutral. Induction strips the first word two letters at a time and "
                    + "uses the quadratic contraction estimate. A length reduction of an even prefix "
                    + "therefore persists after an even suffix is appended."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-neutral-word-high-zero-count"),
                DeclarationHandle.Create(Prefix + "leech_neutral_word_high_zero_count"),
                H("Too many index-zero letters in one direction shorten a word"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the Leech unit charge in basis direction i, the charge polynomial "
                    + "is X(i,0) and the Gram norm is G(i,i) ≥ 4. Put k_i = (G(i,i)+2).toNat. Assume an "
                    + "even word has at least k_i copies of (i,0). Its class lies in the complex span of "
                    + "strictly shorter even neutral words. A permutation collects the k_i copies as an "
                    + "even prefix shortened by the charged power relation. The reduction persists after "
                    + "appending the even suffix."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-neutral-bounded-span"),
                DeclarationHandle.Create(Prefix + "leech_neutral_image_eq_bounded_span"),
                H("Bounded words span the neutral image"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Strong induction on length reduces each even neutral word to "
                    + "ones with total index at most six and strictly fewer than k_i copies of (i,0) in "
                    + "each basis direction i. The selected even words also satisfy the length bound "
                    + "6 + sum_i (k_i - 1). The classes of exactly this family span the neutral image."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-neutral-spanning-classes-finite"),
                DeclarationHandle.Create(Prefix + "leech_neutral_spanning_classes_finite"),
                H("Finiteness of the bounded word family"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every letter in a surviving word has oscillator index between "
                    + "zero and six and one of the finitely many Leech basis labels. Lists over this "
                    + "finite alphabet with the stated length bound form a finite set, and so do the "
                    + "quotient classes of its selected even words."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-fixed-neutral-image-finite"),
                DeclarationHandle.Create(Prefix + "leech_fixed_neutral_image_finite"),
                H("The fixed vacuum-charge image is finite-dimensional"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the actual Leech lattice, the image under the intrinsic fixed "
                    + "quotient map of the sign-fixed carrier supported at vacuum charge is finite-dimensional "
                    + "over the complex numbers. This image is the even-word span, which is generated "
                    + "by the finite family with the stated cutoffs."))),
                DescribeRole.Theorem))));
}
