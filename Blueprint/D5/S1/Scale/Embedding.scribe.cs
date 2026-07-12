using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Scale;

internal sealed class EmbeddingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var a = Id("a");
        var b = Id("b");
        var x = Id("x");
        var coordinates = Add(a, Multiply(b, new Formula.Phi()));
        var embedded = Call("embedding", x);
        var conjugate = Call("conj", x);

        return DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Scale/Embedding",
                "The real embedding of golden integers is an injective ring homomorphism."),
            H("Golden Real Embedding"),
            Blocks(
                Paragraph(
                    Ref("D5/S1/Scale/Embedding"),
                    Text(" sends the golden integer "),
                    Math(coordinates),
                    Text(" to the real number with the same coordinate formula.")),
                new DocumentBlock.Proposition(
                    H("Coordinate formula"),
                    LeanDeclarationRef.Create("D5/S1/Scale/Embedding.embedding_apply"),
                    Blocks(new DocumentBlock.DisplayFormula(
                        Equal(Call("embedding", coordinates), coordinates)))),
                new DocumentBlock.Section(
                    H("Quadratic relation"),
                    Blocks(
                        Paragraph(
                            Text("The defining identity makes the coordinate map multiplicative; "),
                            Math(new Formula.Psi()),
                            Text(" denotes the conjugate root.")),
                        new DocumentBlock.DisplayFormula(
                            Equal(
                                new Formula.Power(new Formula.Phi(), Num(2)),
                                Add(new Formula.Phi(), Num(1)))),
                        new DocumentBlock.DisplayFormula(
                            Equal(
                                new Formula.Psi(),
                                Subtract(Num(1), new Formula.Phi()))),
                        new DocumentBlock.DisplayFormula(
                            new Formula.SetLiteral([new Formula.Phi(), new Formula.Psi()])))),
                new DocumentBlock.Theorem(
                    H("Injectivity"),
                    LeanDeclarationRef.Create("D5/S1/Scale/Embedding.embedding_injective"),
                    Blocks(
                        Paragraph(
                            Text("A coordinate collision with "),
                            Math(NotEqual(b, Num(0))),
                            Text(" would force the forbidden rational identity")),
                        new DocumentBlock.DisplayFormula(
                            Equal(
                                new Formula.Phi(),
                                new Formula.Fraction(new Formula.Negate(a), b))))),
                new DocumentBlock.Section(
                    H("Norm recovery"),
                    Blocks(
                        new DocumentBlock.Theorem(
                            H("Embedding times conjugate"),
                            LeanDeclarationRef.Create(
                                "D5/S1/Scale/Embedding.embedding_mul_conj"),
                            Blocks(new DocumentBlock.DisplayFormula(
                                Equal(
                                    Multiply(embedded, Call("embedding", conjugate)),
                                    Call("norm", x))))),
                        new DocumentBlock.Theorem(
                            H("Absolute norm relation"),
                            LeanDeclarationRef.Create(
                                "D5/S1/Scale/Embedding.abs_embedding_mul_abs_conj"),
                            Blocks(
                                Paragraph(
                                    Text("Taking absolute values gives the corresponding multiplicative relation.")),
                                new DocumentBlock.DisplayFormula(
                                    Equal(
                                        Multiply(
                                            new Formula.Absolute(embedded),
                                            new Formula.Absolute(Call("embedding", conjugate))),
                                        new Formula.Absolute(Call("norm", x)))))))))));
    }
}
