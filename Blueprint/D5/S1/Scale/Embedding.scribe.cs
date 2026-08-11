using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Scale;

internal sealed class EmbeddingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var a = DefinitionDsl.Id("a");
        var b = DefinitionDsl.Id("b");
        var x = DefinitionDsl.Id("x");
        var coordinates = Add(a, Multiply(b, new Formula.Phi()));
        var embedded = Call("embedding", x);
        var conjugate = Call("conj", x);

        return DocumentDefinition.Create(ScribeNode.Create(
            "The real embedding of golden integers is an injective ring homomorphism.",
            H("Golden Real Embedding"),
            Blocks(
                Paragraph(
                    Ref("D5/S1/Scale/Embedding"),
                    Text(" sends the golden integer "),
                    Math(coordinates),
                    Text(" to the real number with the same coordinate formula.")),
                                Describe.Lean(
                    DescribeId.Create("coordinate-formula"),
                    DeclarationHandle.Create(
                        "D5/S1/Scale/Embedding.embedding_apply"),
                    H("Coordinate formula"),
                    StatementSource.FromAuthor(In(Seq(Forall, Sp, F.Id("x"), Sp, InMacro, Sp, Operatorname, Grp(F.Id("GoldenInt")), Comma, Esc, Operatorname, Grp(F.Id("embedding")), Open, F.Id("x"), Close, Eq, F.Id("x"), Dot, F.Id("a"), Plus, F.Id("x"), Dot, F.Id("b"), Varphi))),
                    AssessedProvenance.FromRepo(),
                    Blocks(new DocumentBlock.DisplayFormula(
                        Equal(Call("embedding", coordinates), coordinates))),
                    DescribeRole.Proposition),
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
                                Describe.Lean(
                    DescribeId.Create("injectivity"),
                    DeclarationHandle.Create(
                        "D5/S1/Scale/Embedding.embedding_injective"),
                    H("Injectivity"),
                    StatementSource.FromAuthor(In(Seq(Forall, Sp, F.Id("x"), Comma, F.Id("y"), Sp, InMacro, Sp, Operatorname, Grp(F.Id("GoldenInt")), Comma, Esc, Operatorname, Grp(F.Id("embedding")), Open, F.Id("x"), Close, Eq, Operatorname, Grp(F.Id("embedding")), Open, F.Id("y"), Close, Sp, Rightarrow, Sp, F.Id("x"), Eq, F.Id("y")))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(
                            Text("A coordinate collision with "),
                            Math(NotEqual(b, Num(0))),
                            Text(" would force the forbidden rational identity")),
                        new DocumentBlock.DisplayFormula(
                            Equal(
                                new Formula.Phi(),
                                new Formula.Fraction(new Formula.Negate(a), b)))),
                    DescribeRole.Theorem),
                new DocumentBlock.Section(
                    H("Norm recovery"),
                    Blocks(
                                                Describe.Lean(
                            DescribeId.Create("embedding-times-conjugate"),
                            DeclarationHandle.Create(
                                "D5/S1/Scale/Embedding.embedding_mul_conj"),
                            H("Embedding times conjugate"),
                            StatementSource.FromAuthor(In(Seq(Forall, Sp, F.Id("x"), Sp, InMacro, Sp, Operatorname, Grp(F.Id("GoldenInt")), Comma, Esc, Operatorname, Grp(F.Id("embedding")), Open, F.Id("x"), Close, Operatorname, Grp(F.Id("embedding")), Open, Operatorname, Grp(F.Id("conj")), Open, F.Id("x"), Close, Close, Eq, Operatorname, Grp(F.Id("norm")), Open, F.Id("x"), Close))),
                            AssessedProvenance.FromRepo(),
                            Blocks(new DocumentBlock.DisplayFormula(
                                Equal(
                                    Multiply(embedded, Call("embedding", conjugate)),
                                    Call("norm", x)))),
                            DescribeRole.Theorem),
                                                Describe.Lean(
                            DescribeId.Create("absolute-norm-relation"),
                            DeclarationHandle.Create(
                                "D5/S1/Scale/Embedding.abs_embedding_mul_abs_conj"),
                            H("Absolute norm relation"),
                            StatementSource.FromAuthor(In(Seq(Forall, Sp, F.Id("x"), Sp, InMacro, Sp, Operatorname, Grp(F.Id("GoldenInt")), Comma, Esc, Lvert, Operatorname, Grp(F.Id("embedding")), Open, F.Id("x"), Close, Rvert, Thin, Lvert, Operatorname, Grp(F.Id("embedding")), Open, Operatorname, Grp(F.Id("conj")), Open, F.Id("x"), Close, Close, Rvert, Eq, Lvert, Operatorname, Grp(F.Id("norm")), Open, F.Id("x"), Close, Rvert))),
                            AssessedProvenance.FromRepo(),
                            Blocks(
                                Paragraph(
                                    Text("Taking absolute values gives the corresponding multiplicative relation.")),
                                new DocumentBlock.DisplayFormula(
                                    Equal(
                                        Multiply(
                                            new Formula.Absolute(embedded),
                                            new Formula.Absolute(Call("embedding", conjugate))),
                                        new Formula.Absolute(Call("norm", x))))),
                            DescribeRole.Theorem))))));
    }
}
