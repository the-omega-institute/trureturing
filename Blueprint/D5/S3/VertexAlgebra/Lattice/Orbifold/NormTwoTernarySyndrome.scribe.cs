using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class NormTwoTernarySyndromeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Orbifold/NormTwoTernarySyndrome.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A congruent norm-twelve frame reduces norm-two exclusion to short ternary syndromes.",
        H("Norm-Two Vectors and Ternary Syndromes"),
        Blocks(
            Describe.Lean(DescribeId.Create("norm-two-produces-ternary-word"),
                DeclarationHandle.Create(Prefix + "exists_short_ternary_kernel_word_of_norm_two"),
                H("A norm-two vector produces a kernel word"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The pairing coordinates of a norm-two row have squared norm 24 "
                    + "and share one parity. More than 24 odd coordinates would have larger squared norm. "
                    + "Dividing the even coordinates by two gives squared norm 6. Reduction modulo three "
                    + "therefore gives a nonzero word of weight at most six. The frame identity makes "
                    + "its ternary syndrome zero."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("short-syndromes-exclude-norm-two"),
                DeclarationHandle.Create(Prefix + "bilinear_ne_two_of_short_syndrome_injective"),
                H("Injective short syndromes exclude norm two"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Partition the support of a word of weight at most six into two "
                    + "sets of size at most three. The word is the difference of the two short words "
                    + "obtained by retaining one restriction and negating the other. A nonzero kernel "
                    + "word gives two distinct short words with the same syndrome."))),
                DescribeRole.Theorem))));
}
