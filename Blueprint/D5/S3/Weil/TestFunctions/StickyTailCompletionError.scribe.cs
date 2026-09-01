using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class StickyTailCompletionErrorDocument : IScribeDocumentDefinition
{
    private const string Handle =
        "D5/S3/Weil/TestFunctions/StickyTailCompletionError.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform first-variable Herglotz-kernel derivative estimate gives the "
            + "quantitative sticky-tail completion error bound.",
        H("Sticky-Tail Completion Error"),
        Blocks(Describe.Lean(
            DescribeId.Create("sticky-tail-completion-error"),
            DeclarationHandle.Create(Handle + "sticky_tail_completion_error"),
            H("Sticky-tail positive completion error"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "On the unit circle, the reverse triangle inequality bounds the "
                        + "kernel denominator below by one minus the disk radius. "
                        + "Differentiating in the spectral variable produces a squared "
                        + "denominator and hence the stated uniform constant.")),
                Paragraph(Text(
                    "The completion functions and tail budget are abstract parameters. "
                        + "The source's omitted transport and summation step is represented "
                        + "by an explicit hypothesis that converts the uniform derivative "
                        + "bound into a completion error estimate."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula r = F.Id("r"), budget = F.Id("D"), z = F.Id("z");
        Formula cXi = F.Id("Cxi"), cT = F.Id("CT");
        Formula error = new Formula.Norm(Subtract(Apply(cXi, z), Apply(cT, z)));
        Formula denominator = new Formula.Power(
            Grp(Subtract(D(1), r)),
            D(2));
        Formula constant = new Formula.Fraction(Multiply(D(2), r), denominator);
        Formula conclusion = LessEqual(error, Multiply(constant, budget));

        return Disp(ForAll(
            [
                Bound("r", real),
                Bound("D", real),
                Bound("z", complex),
                Bound("Cxi", Arrow(complex, complex)),
                Bound("CT", Arrow(complex, complex)),
            ],
            conclusion));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula ForAll(
        Formula.BoundVariable[] variables,
        Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
}
