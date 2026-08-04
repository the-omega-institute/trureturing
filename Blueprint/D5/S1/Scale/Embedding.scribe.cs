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
                DocumentBlock.Describe.Proposition(
                    DescribeId.Create("coordinate-formula"),
                    H("Coordinate formula"),

                        LeanTheorem("D5/S1/Scale/Embedding.embedding_apply"),
                    new Formula.Layout(FormulaLayoutMode.Inline, new Formula.LatexSequence([new Formula.LatexMacro(FormulaLatexMacro.Forall), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("x")), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.In), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("GoldenInt"))]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("embedding"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("x")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexWord(FormulaIdentifier.Create("x")), new Formula.LatexSymbol(FormulaLatexSymbol.Period), new Formula.LatexWord(FormulaIdentifier.Create("a")), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexWord(FormulaIdentifier.Create("x")), new Formula.LatexSymbol(FormulaLatexSymbol.Period), new Formula.LatexWord(FormulaIdentifier.Create("b")), new Formula.LatexMacro(FormulaLatexMacro.Varphi)])),
                    DescribeProvenance.RepoDerived(),
                    Blocks(new DocumentBlock.DisplayFormula(
                        Equal(Call("embedding", coordinates), coordinates)))
                ),
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
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("injectivity"),
                    H("Injectivity"),

                        LeanTheorem("D5/S1/Scale/Embedding.embedding_injective"),
                    new Formula.Layout(FormulaLayoutMode.Inline, new Formula.LatexSequence([new Formula.LatexMacro(FormulaLatexMacro.Forall), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("x")), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexWord(FormulaIdentifier.Create("y")), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.In), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("GoldenInt"))]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("embedding"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("x")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("embedding"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("y")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Rightarrow), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("x")), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexWord(FormulaIdentifier.Create("y"))])),
                    DescribeProvenance.RepoDerived(),
                    Blocks(
                        Paragraph(
                            Text("A coordinate collision with "),
                            Math(NotEqual(b, Num(0))),
                            Text(" would force the forbidden rational identity")),
                        new DocumentBlock.DisplayFormula(
                            Equal(
                                new Formula.Phi(),
                                new Formula.Fraction(new Formula.Negate(a), b))))
                ),
                new DocumentBlock.Section(
                    H("Norm recovery"),
                    Blocks(
                        DocumentBlock.Describe.Theorem(
                            DescribeId.Create("embedding-times-conjugate"),
                            H("Embedding times conjugate"),
                            LeanTheorem(
                                "D5/S1/Scale/Embedding.embedding_mul_conj"),
                            new Formula.Layout(FormulaLayoutMode.Inline, new Formula.LatexSequence([new Formula.LatexMacro(FormulaLatexMacro.Forall), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("x")), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.In), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("GoldenInt"))]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("embedding"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("x")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("embedding"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("conj"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("x")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("norm"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("x")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis)])),
                            DescribeProvenance.RepoDerived(),
                            Blocks(new DocumentBlock.DisplayFormula(
                                Equal(
                                    Multiply(embedded, Call("embedding", conjugate)),
                                    Call("norm", x))))
                        ),
                        DocumentBlock.Describe.Theorem(
                            DescribeId.Create("absolute-norm-relation"),
                            H("Absolute norm relation"),
                            LeanTheorem(
                                "D5/S1/Scale/Embedding.abs_embedding_mul_abs_conj"),
                            new Formula.Layout(FormulaLayoutMode.Inline, new Formula.LatexSequence([new Formula.LatexMacro(FormulaLatexMacro.Forall), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("x")), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.In), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("GoldenInt"))]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexMacro(FormulaLatexMacro.Lvert), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("embedding"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("x")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Rvert), new Formula.LatexMacro(FormulaLatexMacro.ThinSpace), new Formula.LatexMacro(FormulaLatexMacro.Lvert), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("embedding"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("conj"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("x")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Rvert), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexMacro(FormulaLatexMacro.Lvert), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("norm"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("x")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Rvert)])),
                            DescribeProvenance.RepoDerived(),
                            Blocks(
                                Paragraph(
                                    Text("Taking absolute values gives the corresponding multiplicative relation.")),
                                new DocumentBlock.DisplayFormula(
                                    Equal(
                                        Multiply(
                                            new Formula.Absolute(embedded),
                                            new Formula.Absolute(Call("embedding", conjugate))),
                                        new Formula.Absolute(Call("norm", x)))))
                        ))))));
    }
}
