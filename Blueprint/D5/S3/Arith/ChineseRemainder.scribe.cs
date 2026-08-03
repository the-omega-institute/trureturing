using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class ChineseRemainderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Arith/ChineseRemainder",
            "The natural map modulo coprime factors is bijective."),
        H("Chinese Remainder Bijectivity"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("the-natural-map-modulo-coprime-factors-is-bijective"),
                H("The natural map modulo coprime factors is bijective"),
                LeanTheorem(
                    "D5/S3/Arith/ChineseRemainder.chinese_remainder_bijective"),
                LatexStatement.Create(
                    @"$$\gcd(m,n)=1 \Rightarrow "
                    + @"\left(\mathbb{Z}/mn\mathbb{Z} \to "
                    + @"\mathbb{Z}/m\mathbb{Z}\times\mathbb{Z}/n\mathbb{Z},\ "
                    + @"x\mapsto(x\operatorname{mod}m,x\operatorname{mod}n)\right)"
                    + @"\text{ is bijective}$$"),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "For coprime natural numbers m and n, the theorem fixes the natural map "
                        + "from integers modulo m times n to the product of the residue rings "
                        + "modulo m and modulo n. Its two readings are the canonical casts to "
                        + "the factor moduli. The conclusion states that this displayed map is "
                        + "bijective, rather than merely asserting that some bijection between "
                        + "the two finite carriers exists.")),
                    Paragraph(Text(
                        "The atom's proof skeleton establishes injectivity from coprimality and "
                        + "then obtains surjectivity by counting the two finite carriers. The "
                        + "formal proof uses Mathlib's ZMod.chineseRemainder ring equivalence, "
                        + "whose forward function is definitionally the same ZMod.castHom natural "
                        + "map displayed in the statement, and assembles the result through the "
                        + "equivalence's bijectivity. This is a faithful library-level assembly of "
                        + "the atomic skeleton under precedent 6.1, and it asserts no numerical "
                        + "certificate.")))
            ))));
}
