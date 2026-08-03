using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class WilsonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Arith/Wilson",
            "The factorial of one less than a prime is congruent to minus one modulo that prime."),
        H("Wilson's Theorem"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("factorial-before-a-prime-is-minus-one-modulo-the-prime"),
                H("The factorial before a prime is minus one modulo the prime"),
                LeanTheorem(
                    "D5/S3/Arith/Wilson.wilson_theorem"),
                LatexStatement.Create(
                    @"$$p\ \text{prime}\quad\Rightarrow\quad (p-1)!\equiv -1\ "
                    + @"(\operatorname{mod}\ p)$$"),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "For every natural prime p, the natural number factorial (p - 1)! casts "
                        + "to -1 in the residue ring ZMod p. Equality after the canonical natural-"
                        + "number cast into ZMod p is the standard formal expression of the "
                        + "congruence (p - 1)! congruent to -1 modulo p, so the statement retains "
                        + "the source atom's modulus, factorial, and sign without weakening.")),
                    Paragraph(Text(
                        "The atomic proof skeleton pairs each nonzero residue modulo p with its "
                        + "multiplicative inverse. Every pair with distinct entries contributes "
                        + "one to the product, while a self-inverse residue solves x squared = 1 "
                        + "and is therefore 1 or -1; their product leaves -1. The Lean proof "
                        + "constructs the required primality Fact from the explicit hypothesis and "
                        + "assembles this skeleton through Mathlib's ZMod.wilsons_lemma. No "
                        + "numerical certificate is asserted.")))
            ))));
}
