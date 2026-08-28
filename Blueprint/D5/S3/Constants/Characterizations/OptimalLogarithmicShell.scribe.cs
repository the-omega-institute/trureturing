using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Characterizations;

internal sealed class OptimalLogarithmicShellDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Constants/Characterizations/OptimalLogarithmicShell."
            + "exp_one_unique_logarithmic_shell_minimizer";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exponential unit is the unique global minimizer of cost per logarithmic scale.",
        H("Optimal Logarithmic Shell"),
        Blocks(Describe.Lean(
            DescribeId.Create("optimal-logarithmic-shell"),
            DeclarationHandle.Create(Declaration),
            H("The logarithmic shell cost is uniquely minimized at exp(1)"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The objective is displayed literally as beta divided by log beta on the "
                        + "source domain beta greater than one. It is not introduced as a "
                        + "target-shaped definition.")),
                Paragraph(Text(
                    "After substituting x = log beta, Mathlib's exponential tangent bound gives "
                        + "the global minimum. Equality would make log(beta/exp(1)) equal to "
                        + "beta/exp(1) - 1; the strict logarithm bound forces that ratio to one."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula beta = Beta;
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula expOne = Call("exp", D(1));
        Formula domain = Seq(Open, D(1), Comma, Sp, Infty, Close);
        Formula cost = Seq(Frac, Grp(beta), Grp(Log, Open, beta, Close));
        Formula minimumCost = Seq(Frac, Grp(expOne), Grp(Log, Open, expOne, Close));
        Formula objective = Seq(Open, beta, Colon, Sp, real, Close, Sp, To, Sp, cost);

        return Disp(Seq(
            Call("IsMinOn", objective, domain, expOne), Sp, Land, RowBreak,
            Forall, Sp, beta, InMacro, Sp, real, Comma, Sp,
            D(1), Sp, Lt, Sp, beta, Comma, Sp,
            cost, Sp, Eq, Sp, minimumCost, Sp, Rightarrow, Sp,
            beta, Sp, Eq, Sp, expOne, Dot));
    }
}
