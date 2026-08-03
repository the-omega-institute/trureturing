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
                DocumentBlock.Describe.Proposition(
                    DescribeId.Create("zero-has-no-scale"),
                    H("Zero has no scale"),

                        LeanTheorem("D5/S1/Scale/Log.logScale_zero"),
                    LatexStatement.Create(@"$\operatorname{logScale}(0)=\operatorname{none}$"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text("The option-valued definition returns `none` at zero.")))
                ),
                DocumentBlock.Describe.Proposition(
                    DescribeId.Create("nonzero-scale"),
                    H("Nonzero scale"),

                        LeanTheorem("D5/S1/Scale/Log.logScale_ne_zero"),
                    LatexStatement.Create(@"$\forall x \in \operatorname{GoldenInt},\ x\neq 0 \Rightarrow \operatorname{logScale}(x)=\operatorname{some}(\lfloor\log_{\varphi}\lvert\operatorname{embedding}(x)\rvert\rfloor)$"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(
                        Paragraph(Text("For nonzero input the following integer is wrapped in `some`:")),
                        new DocumentBlock.DisplayFormula(
                            Equal(
                                Call("logScale", x),
                                Call("some", scaleValue))))
                ),
                new DocumentBlock.Section(
                    H("Integral unit shifts"),
                    Blocks(
                        DocumentBlock.Describe.Proposition(
                            DescribeId.Create("embedding-of-unit-power"),
                            H("Embedding of a unit power"),
                            LeanTheorem(
                                "D5/S1/Scale/Log.embedding_phiUnitZPowMul"),
                            LatexStatement.Create(@"$\forall n \in \mathbb{Z},\ \forall x \in \operatorname{GoldenInt},\ \operatorname{embedding}(\operatorname{phiUnitZPowMul}(n,x))=\varphi^{n}\operatorname{embedding}(x)$"),
                            DescribeProvenance.RepoDerived(),
                            Blocks(new DocumentBlock.DisplayFormula(
                                Equal(
                                    Call("embedding", shifted),
                                    Multiply(
                                        new Formula.Power(new Formula.Phi(), n),
                                        Call("embedding", x)))))
                        ),
                        DocumentBlock.Describe.Theorem(
                            DescribeId.Create("exact-scale-translation"),
                            H("Exact scale translation"),
                            LeanTheorem(
                                "D5/S1/Scale/Log.logScale_phiUnit_zpow_mul"),
                            LatexStatement.Create(@"$\forall n \in \mathbb{Z},\ \forall x \in \operatorname{GoldenInt},\ x\neq 0 \Rightarrow \operatorname{logScale}(\operatorname{phiUnitZPowMul}(n,x))=\operatorname{map}(n+\cdot,\operatorname{logScale}(x))$"),
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
                                            Call("logScale", x)))))
                        ))))));
    }
}
