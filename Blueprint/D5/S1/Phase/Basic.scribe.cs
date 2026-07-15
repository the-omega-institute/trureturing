using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase;

internal sealed class BasicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var n = Id("n");
        var m = Id("m");
        var phaseN = Call("goldenPhase", n);
        var phaseValue = new Formula.Modulo(
            Multiply(n, new Formula.Phi()),
            Num(1));
        var injectivity = LeanTheorem(
            "D5/S1/Phase/Basic.goldenPhase_injective");
        var opening = Paragraph(
            Ref("D5/S1/Phase/Basic"),
            Text(" maps an integer "),
            Math(n),
            Text(" to "),
            Math(phaseValue),
            Text(" in the additive circle. The map preserves zero, addition, and negation."));

        return DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Phase/Basic",
                "Integer golden-ratio phases form an injective additive orbit on the unit circle."),
            H("Golden Phase"),
            Blocks(
                opening,
                new DocumentBlock.DisplayFormula(Equal(phaseN, phaseValue)),
                new DocumentBlock.Section(
                    H("Additive laws"),
                    Blocks(
                        new DocumentBlock.Describe(
                            DescribeId.Create("zero"),
                            DescribeKind.Proposition,
                            H("Zero"),
                            DescribeStatement.FromLean(
                                LeanTheorem("D5/S1/Phase/Basic.goldenPhase_zero")),
                            DescribeProvenance.RepoDerived(),
                            Blocks(new DocumentBlock.DisplayFormula(
                                Equal(Call("goldenPhase", Num(0)), Num(0))))),
                        new DocumentBlock.Describe(
                            DescribeId.Create("addition"),
                            DescribeKind.Proposition,
                            H("Addition"),
                            DescribeStatement.FromLean(
                                LeanTheorem("D5/S1/Phase/Basic.goldenPhase_add")),
                            DescribeProvenance.RepoDerived(),
                            Blocks(new DocumentBlock.DisplayFormula(
                                Equal(
                                    Call("goldenPhase", Add(n, m)),
                                    Add(phaseN, Call("goldenPhase", m)))))),
                        new DocumentBlock.Describe(
                            DescribeId.Create("negation"),
                            DescribeKind.Proposition,
                            H("Negation"),
                            DescribeStatement.FromLean(
                                LeanTheorem("D5/S1/Phase/Basic.goldenPhase_neg")),
                            DescribeProvenance.RepoDerived(),
                            Blocks(new DocumentBlock.DisplayFormula(
                                Equal(
                                    Call("goldenPhase", new Formula.Negate(n)),
                                    new Formula.Negate(phaseN))))))),
                new DocumentBlock.Section(
                    H("Orbit notation"),
                    Blocks(
                        Paragraph(
                            Text("The same orbit has sequence and set presentations:")),
                        new DocumentBlock.DisplayFormula(
                            Equal(new Formula.Subscript(Id("p"), n), phaseValue)),
                        new DocumentBlock.DisplayFormula(
                            new Formula.Sequence(phaseValue, n, new Formula.Integers())),
                        new DocumentBlock.DisplayFormula(
                            new Formula.SetBuilder(phaseValue, n, new Formula.Integers())))),
                new DocumentBlock.Describe(
                    DescribeId.Create("injectivity"),
                    DescribeKind.Theorem,
                    H("Injectivity"),
                    DescribeStatement.FromLean(injectivity),
                    DescribeProvenance.RepoDerived(),
                    Blocks(
                        Paragraph(
                            Text("Two phases could coincide only if a nonzero integer multiple of "),
                            Math(new Formula.Phi()),
                            Text(" were an integer. Irrationality excludes this. No three-distance theorem is asserted here.")))))));
    }
}
