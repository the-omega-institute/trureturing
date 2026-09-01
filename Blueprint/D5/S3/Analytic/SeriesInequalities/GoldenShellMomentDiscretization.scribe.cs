using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SeriesInequalities;

internal sealed class GoldenShellMomentDiscretizationDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden geometric shells recover every positive finite defect moment within a fixed factor.",
        H("Golden Shell Moment Discretization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-shell-moment-discretization"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/SeriesInequalities/"
                    + "GoldenShellMomentDiscretization."
                    + "golden_shell_moment_sandwich"),
                H("Golden shells give a multiplicative moment sandwich"),
                StatementSource.FromAuthor(SandwichFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a finite family of defects carry nonnegative real weights. Assign "
                        + "each defect delta(i) to the unique supplied shell n(i), between the "
                        + "successive radii omega(n(i)+1) and omega(n(i)). For every positive "
                        + "real exponent s, its exact weighted moment lies between the golden "
                        + "shell transcript and phi^(-2s) times that transcript.")),
                    Paragraph(Text(
                        "The shell radius is omega(n)=(1/2) phi^(-2n). Consecutive radii differ "
                        + "by the positive ratio phi^(-2). Positive real powers preserve each "
                        + "pointwise shell inequality, nonnegative weights preserve order, and "
                        + "finite summation gives the displayed sandwich.")),
                    Paragraph(Text(
                        "Finite indexing is the finite-support specialization of the source's "
                        + "shell charges. It removes convergence assumptions without changing "
                        + "the regrouped weighted sum. The positive-exponent and nonnegative-weight "
                        + "hypotheses are explicit because reversing either sign can reverse the "
                        + "claimed inequalities.")),
                    Paragraph(Text(
                        "The module also proves the exponent-two factor phi^(-4). A singleton at "
                        + "delta=1/2 computes both second moments as 1/4; moving it to delta=1 "
                        + "breaks the shell premise and computes the exact moment as 1 while the "
                        + "transcript remains 1/4, so the upper conclusion is false."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula SandwichFormula()
    {
        Formula real = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        Formula natural = F.Seq(F.Mathbb, F.Grp(F.Id("N")));
        Formula indexType = F.Iota;
        Formula index = F.Id("i");
        Formula weight = F.Id("m");
        Formula defect = F.DeltaLower;
        Formula shell = F.Id("n");
        Formula exponent = F.Id("s");
        Formula omega = F.Omega;
        Formula transcript = Apply(
            new Formula.Subscript(F.Seq(F.Mathcal, F.Grp(F.Id("G"))), F.Perp),
            exponent);
        Formula exactMoment = Apply(
            new Formula.Subscript(F.Zeta, F.Perp),
            exponent);
        Formula shellAt = Apply(shell, index);
        Formula weightAt = Apply(weight, index);
        Formula defectAt = Apply(defect, index);
        Formula upperRadius = Apply(omega, shellAt);
        Formula lowerRadius = Apply(
            omega,
            F.Seq(shellAt, F.Sp, F.Plus, F.Sp, F.D(1)));

        Formula nonnegativeWeights = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType)],
            LessThanOrEqual(F.D(0), weightAt));
        Formula shellBounds = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType)],
            And(
                LessThan(lowerRadius, defectAt),
                LessThanOrEqual(defectAt, upperRadius)));
        Formula hypotheses = And(
            Call("Finite", indexType),
            And(
                LessThan(F.D(0), exponent),
                And(nonnegativeWeights, shellBounds)));
        Formula lowerFactor = F.Seq(
            F.Varphi, F.Caret,
            F.Grp(F.Minus, F.D(2), exponent));
        Formula conclusion = And(
            LessThanOrEqual(
                F.Seq(lowerFactor, F.Sp, F.Cdot, F.Sp, transcript),
                exactMoment),
            LessThanOrEqual(exactMoment, transcript));

        return F.Disp(F.Seq(
            F.Begin, F.Grp(F.Id("gathered")),
            F.Forall, F.Sp, indexType, F.Comma, F.RowBreak,
            weight, F.Comma, F.Sp, defect, F.Colon, F.Sp,
            indexType, F.To, F.Sp, real, F.Comma, F.RowBreak,
            shell, F.Colon, F.Sp, indexType, F.To, F.Sp, natural,
            F.Comma, F.Sp, exponent, F.InMacro, real, F.Comma, F.RowBreak,
            hypotheses, F.Sp, F.Rightarrow, F.RowBreak,
            conclusion, F.Dot,
            F.End, F.Grp(F.Id("gathered"))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        F.Seq(F.Operatorname, F.Grp(F.Id(name)), F.Open, F.Seq(arguments), F.Close);
}
