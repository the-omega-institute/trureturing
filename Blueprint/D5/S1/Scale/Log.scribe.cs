using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Scale;

internal sealed class LogDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var n = Id("n");
        var x = Id("x");
        var scaleValue = new Formula.Floor(
            new Formula.Log(
                new Formula.Phi(),
                new Formula.Absolute(Call("embedding", x))));
        var shifted = Call("phiUnitZPowMul", n, x);

        return DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Scale/Log",
                "Nonzero golden integers have an integer logarithmic scale with exact unit shifts."),
            H("Golden Logarithmic Scale"),
            Blocks(
                Paragraph(
                    Ref("D5/S1/Scale/Log"),
                    Text(" assigns a scale only when "),
                    Math(NotEqual(x, Num(0))),
                    Text(". Zero is represented by `none`, never by a fabricated integer.")),
                new DocumentBlock.Describe(
                    DescribeId.Create("zero-has-no-scale"),
                    DescribeKind.Proposition,
                    H("Zero has no scale"),
                    DescribeStatement.FromLean(
                        LeanTheorem("D5/S1/Scale/Log.logScale_zero")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text("The option-valued definition returns `none` at zero."))),
                    LatexStatement.Create(@"$\operatorname{logScale}(0)=\operatorname{none}$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("nonzero-scale"),
                    DescribeKind.Proposition,
                    H("Nonzero scale"),
                    DescribeStatement.FromLean(
                        LeanTheorem("D5/S1/Scale/Log.logScale_ne_zero")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(
                        Paragraph(Text("For nonzero input the following integer is wrapped in `some`:")),
                        new DocumentBlock.DisplayFormula(
                            Equal(
                                Call("logScale", x),
                                Call("some", scaleValue)))),
                    LatexStatement.Create(@"$\forall x \in \operatorname{GoldenInt},\ x\neq 0 \Rightarrow \operatorname{logScale}(x)=\operatorname{some}(\lfloor\log_{\varphi}\lvert\operatorname{embedding}(x)\rvert\rfloor)$")),
                new DocumentBlock.Section(
                    H("Integral unit shifts"),
                    Blocks(
                        new DocumentBlock.Describe(
                            DescribeId.Create("embedding-of-unit-power"),
                            DescribeKind.Proposition,
                            H("Embedding of a unit power"),
                            DescribeStatement.FromLean(LeanTheorem(
                                "D5/S1/Scale/Log.embedding_phiUnitZPowMul")),
                            DescribeProvenance.RepoDerived(),
                            Blocks(new DocumentBlock.DisplayFormula(
                                Equal(
                                    Call("embedding", shifted),
                                    Multiply(
                                        new Formula.Power(new Formula.Phi(), n),
                                        Call("embedding", x))))),
                            LatexStatement.Create(@"$\forall n \in \mathbb{Z},\ \forall x \in \operatorname{GoldenInt},\ \operatorname{embedding}(\operatorname{phiUnitZPowMul}(n,x))=\varphi^{n}\operatorname{embedding}(x)$")),
                        new DocumentBlock.Describe(
                            DescribeId.Create("exact-scale-translation"),
                            DescribeKind.Theorem,
                            H("Exact scale translation"),
                            DescribeStatement.FromLean(LeanTheorem(
                                "D5/S1/Scale/Log.logScale_phiUnit_zpow_mul")),
                            DescribeProvenance.RepoDerived(),
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
                            LatexStatement.Create(@"$\forall n \in \mathbb{Z},\ \forall x \in \operatorname{GoldenInt},\ x\neq 0 \Rightarrow \operatorname{logScale}(\operatorname{phiUnitZPowMul}(n,x))=\operatorname{map}(n+\cdot,\operatorname{logScale}(x))$")))))));
    }
}
