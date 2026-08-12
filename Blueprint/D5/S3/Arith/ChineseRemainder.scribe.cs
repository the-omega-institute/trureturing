using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class ChineseRemainderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The natural map modulo coprime factors is bijective.",
        H("Chinese Remainder Bijectivity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-natural-map-modulo-coprime-factors-is-bijective"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/ChineseRemainder.chinese_remainder_bijective"),
                H("The natural map modulo coprime factors is bijective"),
                StatementSource.FromAuthor(Disp(Seq(Gcd, Open, F.Id("m"), Comma, F.Id("n"), Close, Eq, D(1), Sp, Rightarrow, Sp, Left, Open, Mathbb, Grp(F.Id("Z")), Slash, F.Id("mn"), Mathbb, Grp(F.Id("Z")), Sp, To, Sp, Mathbb, Grp(F.Id("Z")), Slash, F.Id("m"), Mathbb, Grp(F.Id("Z")), Times, Mathbb, Grp(F.Id("Z")), Slash, F.Id("n"), Mathbb, Grp(F.Id("Z")), Comma, Esc, F.Id("x"), Mapsto, Open, F.Id("x"), Operatorname, Grp(F.Id("mod")), F.Id("m"), Comma, F.Id("x"), Operatorname, Grp(F.Id("mod")), F.Id("n"), Close, Right, Close, F.Text, Grp(Sp, F.Id("is"), Sp, F.Id("bijective"))))),
                AssessedProvenance.FromRepo(),
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
                        + "certificate."))),
                DescribeRole.Theorem))));
}
