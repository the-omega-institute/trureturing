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
                "Nonzero golden integers have an integer logarithmic scale with exact unit shifts.",
                AnchorCatalogDefinitions.GictI2Definition1_4),
            H("Golden Logarithmic Scale"),
            Blocks(
                Paragraph(
                    Ref("D5/S1/Scale/Log"),
                    Text(" assigns a scale only when "),
                    Math(NotEqual(x, Num(0))),
                    Text(". Zero is represented by `none`, never by a fabricated integer.")),
                new DocumentBlock.Proposition(
                    H("Zero has no scale"),
                    LeanTheorem("D5/S1/Scale/Log.logScale_zero"),
                    Blocks(Paragraph(Text("The option-valued definition returns `none` at zero.")))),
                new DocumentBlock.Proposition(
                    H("Nonzero scale"),
                    LeanTheorem("D5/S1/Scale/Log.logScale_ne_zero"),
                    Blocks(
                        Paragraph(Text("For nonzero input the following integer is wrapped in `some`:")),
                        new DocumentBlock.DisplayFormula(
                            Equal(
                                Call("logScale", x),
                                Call("some", scaleValue))))),
                new DocumentBlock.Section(
                    H("Integral unit shifts"),
                    Blocks(
                        new DocumentBlock.Proposition(
                            H("Embedding of a unit power"),
                            LeanTheorem(
                                "D5/S1/Scale/Log.embedding_phiUnitZPowMul"),
                            Blocks(new DocumentBlock.DisplayFormula(
                                Equal(
                                    Call("embedding", shifted),
                                    Multiply(
                                        new Formula.Power(new Formula.Phi(), n),
                                        Call("embedding", x)))))),
                        new DocumentBlock.Theorem(
                            H("Exact scale translation"),
                            LeanTheorem(
                                "D5/S1/Scale/Log.logScale_phiUnit_zpow_mul"),
                            Blocks(
                                Paragraph(
                                    Text("At the option level, every integer exponent, including negative powers, translates the scale through `map` exactly:")),
                                new DocumentBlock.DisplayFormula(
                                    Equal(
                                        Call("logScale", shifted),
                                        Call(
                                            "map",
                                            Add(n, new Formula.Placeholder()),
                                            Call("logScale", x)))))))))));
    }
}
