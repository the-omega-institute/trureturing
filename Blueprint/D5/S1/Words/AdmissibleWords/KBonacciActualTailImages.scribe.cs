using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AdmissibleWords;

internal sealed class KBonacciActualTailImagesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal terminal-one and trailing-zero conditions give exact image decompositions "
            + "for actual admissible Boolean words over any commutative ring.",
        H("Exact suffix images of actual words"),
        Blocks(
            Paragraph(Text(
                "Fix a commutative ring C, a point x in C, and an order k at least two. "
                    + "A word of length n is a function from Fin n to Bool, accepted by the "
                    + "original scanner forbidding k consecutive true bits. Its value is the "
                    + "sum of x^j over its true positions, counted from the constant term. "
                    + "Let I_n be the set of values of these accepted length-n words, and "
                    + "let S_s be the sum of x^j for zero at most j below s.")),
            Paragraph(Text(
                "T_(n,s) imposes s at most n, true bits in the final s positions, and a "
                    + "false bit at position n-s-1 whenever that position exists. Z_(n,z) "
                    + "imposes z at most n and false bits in the final z positions. Both "
                    + "sets use the same actual accepted words as I_n.")),
            Describe.Lean(
                DescribeId.Create("kbonacci-actual-tail-zero-image-decomposition"),
                DeclarationHandle.Create(
                    "D5/S1/Words/AdmissibleWords/KBonacciActualTailImages."
                        + "actual_tail_zero_image_decomposition"),
                H("All terminal-one and trailing-zero branches"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("T"), Underscore, Grp(F.Id("n"), Comma, F.Id("s")), Eq,
                    Begin, Grp(F.Id("cases")),
                    Emptyset, Amp, F.Id("n"), Lt, F.Id("s"), RowBreak,
                    OpenBrace, F.Id("S"), Underscore, F.Id("s"), CloseBrace,
                    Amp, F.Id("n"), Eq, F.Id("s"), RowBreak,
                    F.Id("I"), Underscore, Grp(F.Id("n"), Minus, F.Id("s"), Minus, D(1)),
                    Plus, F.Id("x"), Caret, Grp(F.Id("n"), Minus, F.Id("s")),
                    F.Id("S"), Underscore, F.Id("s"), Amp,
                    F.Id("s"), Plus, D(1), Leq, Sp, F.Id("n"),
                    End, Grp(F.Id("cases")), Qquad, Land, Qquad, Sp,
                    F.Id("Z"), Underscore, Grp(F.Id("n"), Comma, F.Id("z")), Eq,
                    Begin, Grp(F.Id("cases")),
                    Emptyset, Amp, F.Id("n"), Lt, F.Id("z"), RowBreak,
                    F.Id("I"), Underscore, Grp(F.Id("n"), Minus, F.Id("z")),
                    Amp, F.Id("z"), Leq, Sp, F.Id("n"),
                    End, Grp(F.Id("cases"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The equations hold for every natural n, every s below k, and every "
                            + "positive z. At n=s the only word is the all-true word, including "
                            + "the empty word when s=0. For n at least s+1, every exact-tail "
                            + "word has the form v followed by a false bit and then s true "
                            + "bits, with v of length n-s-1.")),
                    Paragraph(Text(
                        "Deleting the suffix preserves acceptance. Conversely, the scanner "
                            + "through a prefix followed by a false delimiter is the conjunction "
                            + "of its prefix scan and a fresh full-budget scan of the remaining "
                            + "suffix. This equation preserves rejection of the prefix, and "
                            + "the true suffix is accepted because s is below k. The suffix "
                            + "contributes x^(n-s) times S_s to the value.")),
                    Paragraph(Text(
                        "A word with z trailing false bits is a legal prefix of length n-z "
                            + "followed by z actual zero positions. Those positions preserve "
                            + "acceptance and value. A suffix longer than the actual word is "
                            + "impossible. Ring multiplication and addition are those of C; "
                            + "when C is a common polynomial image subring, the same one "
                            + "polynomial supplies every quotient coordinate."))),
                DescribeRole.Theorem))));
}
