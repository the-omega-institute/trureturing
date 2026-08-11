using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Scale;

internal sealed class LogDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var n = DefinitionDsl.Id("n");
        var x = DefinitionDsl.Id("x");
        var scaleValue = new Formula.Floor(
            new Formula.Log(
                new Formula.Phi(),
                new Formula.Absolute(Call("embedding", x))));
        var shifted = Call("phiUnitZPowMul", n, x);

        return DocumentDefinition.Create(ScribeNode.Create(
            "Nonzero golden integers have an integer logarithmic scale with exact unit shifts.",
            H("Golden Logarithmic Scale"),
            Blocks(
                Paragraph(
                    Ref("D5/S1/Scale/Log"),
                    Text(" assigns a scale only when "),
                    Math(NotEqual(x, Num(0))),
                    Text(". Zero is represented by `none`, never by a fabricated integer.")),
                                Describe.Lean(
                    DescribeId.Create("zero-has-no-scale"),
                    DeclarationHandle.Create(
                        "D5/S1/Scale/Log.logScale_zero"),
                    H("Zero has no scale"),
                    StatementSource.FromAuthor(In(Seq(Operatorname, Grp(F.Id("logScale")), Open, D(0), Close, Eq, Operatorname, Grp(F.Id("none"))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The option-valued definition returns `none` at zero."))),
                    DescribeRole.Proposition),
                                Describe.Lean(
                    DescribeId.Create("nonzero-scale"),
                    DeclarationHandle.Create(
                        "D5/S1/Scale/Log.logScale_ne_zero"),
                    H("Nonzero scale"),
                    StatementSource.FromAuthor(In(Seq(Forall, Sp, F.Id("x"), Sp, InMacro, Sp, Operatorname, Grp(F.Id("GoldenInt")), Comma, Esc, F.Id("x"), Neq, Sp, D(0), Sp, Rightarrow, Sp, Operatorname, Grp(F.Id("logScale")), Open, F.Id("x"), Close, Eq, Operatorname, Grp(F.Id("some")), Open, Lfloor, Log, Underscore, Grp(Varphi), Lvert, Operatorname, Grp(F.Id("embedding")), Open, F.Id("x"), Close, Rvert, Rfloor, Close))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For nonzero input the following integer is wrapped in `some`:")),
                        new DocumentBlock.DisplayFormula(
                            Equal(
                                Call("logScale", x),
                                Call("some", scaleValue)))),
                    DescribeRole.Proposition),
                new DocumentBlock.Section(
                    H("Integral unit shifts"),
                    Blocks(
                                                Describe.Lean(
                            DescribeId.Create("embedding-of-unit-power"),
                            DeclarationHandle.Create(
                                "D5/S1/Scale/Log.embedding_phiUnitZPowMul"),
                            H("Embedding of a unit power"),
                            StatementSource.FromAuthor(In(Seq(Forall, Sp, F.Id("n"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Esc, Forall, Sp, F.Id("x"), Sp, InMacro, Sp, Operatorname, Grp(F.Id("GoldenInt")), Comma, Esc, Operatorname, Grp(F.Id("embedding")), Open, Operatorname, Grp(F.Id("phiUnitZPowMul")), Open, F.Id("n"), Comma, F.Id("x"), Close, Close, Eq, Varphi, Caret, Grp(F.Id("n")), Operatorname, Grp(F.Id("embedding")), Open, F.Id("x"), Close))),
                            AssessedProvenance.FromRepo(),
                            Blocks(new DocumentBlock.DisplayFormula(
                                Equal(
                                    Call("embedding", shifted),
                                    Multiply(
                                        new Formula.Power(new Formula.Phi(), n),
                                        Call("embedding", x))))),
                            DescribeRole.Proposition),
                                                Describe.Lean(
                            DescribeId.Create("exact-scale-translation"),
                            DeclarationHandle.Create(
                                "D5/S1/Scale/Log.logScale_phiUnit_zpow_mul"),
                            H("Exact scale translation"),
                            StatementSource.FromAuthor(In(Seq(Forall, Sp, F.Id("n"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Esc, Forall, Sp, F.Id("x"), Sp, InMacro, Sp, Operatorname, Grp(F.Id("GoldenInt")), Comma, Esc, F.Id("x"), Neq, Sp, D(0), Sp, Rightarrow, Sp, Operatorname, Grp(F.Id("logScale")), Open, Operatorname, Grp(F.Id("phiUnitZPowMul")), Open, F.Id("n"), Comma, F.Id("x"), Close, Close, Eq, Operatorname, Grp(F.Id("map")), Open, F.Id("n"), Plus, Cdot, Comma, Operatorname, Grp(F.Id("logScale")), Open, F.Id("x"), Close, Close))),
                            AssessedProvenance.FromRepo(),
                            Blocks(
                                Paragraph(
                                    Text("At the option level, every integer exponent, including negative powers, translates the scale through `map` exactly:")),
                                new DocumentBlock.DisplayFormula(
                                    Equal(
                                        Call("logScale", shifted),
                                        Call(
                                            "map",
                                            Add(n, new Formula.Placeholder()),
                                            Call("logScale", x))))),
                            DescribeRole.Theorem))))));
    }
}
