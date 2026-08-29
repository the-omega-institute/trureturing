using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Budget;

internal sealed class ProjectiveStrongDualityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite attained dual minima converge exactly to the full primal value.",
        H("Projective Strong Duality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("projective-strong-duality"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Budget/ProjectiveStrongDuality."
                        + "projective_strong_duality"),
                H("The finite strong-duality tower has no projective gap"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The point carrier and the dependent family of finite test spaces are "
                            + "public. The circle slack, evaluation at zero, pairing, budget, "
                            + "finite primal values, and full primal value are all supplied on "
                            + "those carriers.")),
                    Paragraph(Text(
                        "Every finite dual-value set is constructed from a nonnegative pressure, "
                            + "the pointwise circle-slack inequality, the Haar-floor inequality, "
                            + "and the affine pairing-plus-budget objective. Finite strong duality "
                            + "states that the corresponding primal value is its least element.")),
                    Paragraph(Text(
                        "Nonnegativity bounds the decreasing primal tower below. Pinned Mathlib "
                            + "monotone convergence identifies its infimum with the supplied full "
                            + "limit, while each finite least-element certificate rewrites that "
                            + "infimum as the attained finite dual minimum.")),
                    Paragraph(Text(
                        "The public conclusion also returns a feasible minimizer at every finite "
                            + "stage. It makes no assertion that one test and pressure pair attains "
                            + "the full infinite-dimensional dual."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula point = F.Id("Point");
        Formula test = F.Id("Test");
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula stage = F.Id("N");
        Formula z = F.Id("z");
        Formula phi = F.Id("phi");
        Formula psi = F.Id("psi");
        Formula theta = F.Id("theta");
        Formula eta = F.Id("eta");
        Formula value = F.Id("x");
        Formula circle = F.Id("Gamma");
        Formula atZero = F.Id("e0");
        Formula pairing = F.Id("W");
        Formula scale = F.Id("a");
        Formula budget = F.Id("C");
        Formula primal = F.Id("Lambda");
        Formula full = Sub(F.Id("Lambda"), Infty);
        Formula testAtStage = Apply(test, stage);
        Formula primalAtStage = Apply(primal, stage);

        Formula Objective(Formula candidate, Formula pressure) => Seq(
            Apply(pairing, stage, candidate), Sp, Plus, Sp,
            pressure, budget);

        Formula Feasible(Formula candidate, Formula pressure) => Seq(
            D(0), Sp, Leq, Sp, pressure, Sp, Land, Sp,
            Open, Forall, Sp, Typed(z, point), Comma, Sp,
            D(0), Sp, Leq, Sp, Apply(circle, stage, candidate, z), Sp,
            Plus, Sp, pressure, Close, Sp, Land, Sp,
            D(2), scale, Sp, Leq, Sp,
            D(2), scale, Apply(atZero, stage, candidate), Sp,
            Plus, Sp, pressure);

        Formula dualValues = Seq(
            OpenBrace, value, InMacro, Sp, real, Sp, Mid, Sp,
            Exists, Sp, Typed(phi, testAtStage), Comma, Sp,
            Exists, Sp, Typed(theta, real), Comma, Sp,
            Feasible(phi, theta), Sp, Land, Sp,
            value, Sp, Eq, Sp, Objective(phi, theta), CloseBrace);
        Formula dualValuesAtStage = Sub(F.Id("D"), stage);
        Formula dualDefinition = Seq(
            Typed(F.Id("D"), Arrow(natural, Call("Set", real))), Comma, Sp,
            Forall, Sp, Typed(stage, natural), Comma, Sp,
            dualValuesAtStage, Sp, Eq, Sp, dualValues);
        Formula finiteLeast = Seq(
            Forall, Sp, Typed(stage, natural), Comma, Sp,
            Call("IsLeast", dualValuesAtStage, primalAtStage));
        Formula stageOptimizer = Seq(
            Forall, Sp, Typed(stage, natural), Comma, Sp,
            Exists, Sp, Typed(phi, testAtStage), Comma, Sp,
            Exists, Sp, Typed(theta, real), Comma, Sp,
            Feasible(phi, theta), Sp, Land, Sp,
            Call("sInf", dualValuesAtStage), Sp, Eq, Sp,
            Objective(phi, theta));
        Formula projectiveInfimum = Seq(
            full, Sp, Eq, Sp, Operatorname, Grp(F.Id("inf")), Underscore,
            Grp(stage, InMacro, natural), Sp,
            Call("sInf", dualValuesAtStage));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(point, type), Comma, Sp,
                Typed(test, Arrow(natural, type)), Comma),
            Seq(
                Typed(circle, Call("DependentMap", Typed(stage, natural), testAtStage,
                    Arrow(point, real))), Comma),
            Seq(
                Typed(atZero, Call("DependentMap", Typed(stage, natural), testAtStage, real)),
                Comma, Sp,
                Typed(pairing, Call("DependentMap", Typed(stage, natural), testAtStage, real)),
                Comma),
            Seq(
                Typed(scale, real), Comma, Sp, Typed(budget, real), Comma, Sp,
                Typed(primal, Arrow(natural, real)), Comma, Sp, Typed(full, real), Comma),
            Seq(
                Operatorname, Grp(F.Id("let")), Open,
                dualDefinition, Close, SemiSpace),
            Seq(
                Open, Forall, Sp, Typed(stage, natural), Comma, Sp,
                D(0), Sp, Leq, Sp, primalAtStage, Close, Sp, Land, Sp,
                Call("Antitone", primal), Sp, Land),
            Seq(
                Call("Tendsto", primal, Call("atTop", natural), Call("nhds", full)), Sp,
                Land, Sp, Open, finiteLeast, Close),
            Seq(
                Rightarrow, Sp, projectiveInfimum, Sp, Land),
            Seq(
                stageOptimizer, Dot),
        ]));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Sub(Formula value, Formula index) =>
        new Formula.Subscript(value, index);

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);
}
