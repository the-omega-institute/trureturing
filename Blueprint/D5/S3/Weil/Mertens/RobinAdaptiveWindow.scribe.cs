using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens;

internal sealed class RobinAdaptiveWindowDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Weil/Mertens/RobinAdaptiveWindow.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adaptive sampling of the whole Robin window",
        H("Constant error with a fourth-root sample count"),
        Blocks(
            Describe.Lean(DescribeId.Create("robin-adaptive-window-sampling"),
                DeclarationHandle.Create(Module + "window_sampling"), H("Whole-window sampling bound"),
                StatementSource.FromAuthor(Sampling()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("M is the actual weighted negative mass and P sums the weighted "
                        + "positive parts of signed chords in the coordinate u(t)=t log(t). "
                        + "N counts distinct endpoint samples, m counts doubling blocks, and "
                        + "C=1/(1−2^(−1/6)).")),
                    Paragraph(Text("Clip the final doubling block at B. In a block starting at a, "
                        + "an equally spaced mesh with step at most (a/B)^(1/12) times a^(3/4) "
                        + "has error at most 9(a/B)^(1/6). The same geometric weight bounds "
                        + "the cell count after division by B^(1/4) and allowance for the ceiling.")),
                    Paragraph(Text("Each block contributes its left and interior nodes. Insert B "
                        + "once to obtain exactly one more distinct sample than the total cell count. "
                        + "The equal-endpoint window has one sample and zero chord mass. "
                        + "All signed values can use the same Mangoldt cutoff at the floor of B."))),
                DescribeRole.Theorem))));

    private static Formula At(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);

    private static Formula Sampling()
    {
        var a = F.Id("A");
        var b = F.Id("B");
        var c = F.Id("C");
        var count = At("N", a, b);
        var quarterPower = Seq(b, Caret, Grp(new Formula.Fraction(D(1), D(4))));
        var error = new Formula.Absolute(Subtract(At("M", a, b), At("P", a, b)));
        var bound = And(Le(error, Multiply(D(9), c)),
            And(Le(count, Add(Add(Multiply(c, quarterPower), At("m", a, b)), D(1))),
                Le(count, Add(Multiply(Multiply(D(2), c), quarterPower), D(1)))));
        var real = Seq(Mathbb, Grp(F.Id("R")));
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("A"), real,
            new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("B"), real,
                Implies(Le(At("exp", D(1)), a), Implies(Le(a, b), bound)))));
    }
}
