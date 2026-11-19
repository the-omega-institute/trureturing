using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Dilation;

internal sealed class DuplicationQuadraticGermDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Analytic/kuczma1964cosine");
    private const string Declaration =
        "D5/S3/Analytic/Dilation/DuplicationQuadraticGerm.eq_cos_of_quadratic_germ";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A bounded duplication solution with a prescribed quadratic germ is a cosine.",
        H("Duplication and the Quadratic Germ"),
        Blocks(Describe.Lean(
            DescribeId.Create("cosine-quadratic-germ"),
            DeclarationHandle.Create(
                "D5/S3/Analytic/Dilation/DuplicationQuadraticGerm.cosine_quadratic_germ"),
            H("The cosine quadratic germ"),
            StatementSource.FromAuthor(CosineGermFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For every real k, the difference between cos(kt) and 1-k^2 t^2/2 is o(t^2) "
                + "in the full neighborhood filter at zero. This auxiliary expansion is consumed "
                + "by the global uniqueness theorem below."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("bounded-duplication-quadratic-germ"),
            DeclarationHandle.Create(Declaration),
            H("The germ determines the global solution"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text(
                    "Let f be a real-valued function on the real line, with absolute value at most one, "
                    + "and let k be any real number. Assume the duplication equation "
                    + "f(2t)=2f(t)^2-1 and the quadratic expansion f(t)=1-k^2 t^2/2+o(t^2) at zero. "
                    + "Then f(t)=cos(kt) for every real t. Taking k to be the nonnegative square root "
                    + "of twice a nonnegative quadratic coefficient gives the corresponding coefficient formulation.")),
                Paragraph(Text(
                    "The little-o relation uses the full neighborhood filter at zero, including the value there. "
                    + "In particular the expansion forces f(0)=1. If a punctured neighborhood is used instead, "
                    + "the value f(0)=1 must be supplied separately; otherwise the duplication equation "
                    + "also permits the isolated value f(0)=-1/2.")),
                Paragraph(Text(
                    "For two bounded duplication solutions f and g, one doubling multiplies their absolute "
                    + "difference by at most four. After n doublings, the difference at t is bounded by "
                    + "4^n times the difference at t/2^n. If their difference is o(t^2) at zero, this bound "
                    + "is arbitrarily small, and the two functions agree everywhere.")),
                Paragraph(Text(
                    "The cosine has the required quadratic germ because its remainder is "
                    + "(k^2/2)(1-sinc(kt/2)^2)t^2 and sinc is continuous with value one at zero. "
                    + "The double-angle identity then supplies the comparison solution. "
                    + "No differentiability of f away from zero is assumed.")),
                Paragraph(Text(
                    "The duplication equation and earlier cosine characterizations are classical. "
                    + "Kuczma reports Forder's uniqueness result for even solutions twice differentiable "
                    + "at zero, and proves characterizations with continuity and periodicity assumptions. "
                    + "Those statements do not have the precise bounded quadratic-germ hypotheses here. "
                    + "This citation does not assert priority for the remainder formulation."))),
            DescribeRole.Theorem))));

    private static Formula Reals => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Pow(Formula value) => new Formula.Power(value, F.D(2));
    private static Formula Mul(Formula left, Formula right) =>
        F.Seq(F.Open, left, F.Sp, F.Cdot, F.Sp, right, F.Close);
    private static Formula Sub(Formula left, Formula right) =>
        F.Seq(F.Open, left, F.Minus, right, F.Close);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Lambda(string name, Formula body) =>
        F.Seq(F.Open, F.Id(name), F.Colon, F.Sp, Reals, F.Sp, F.Mapsto, F.Sp, body, F.Close);

    private static Formula CosineGermFormula()
    {
        Formula k = F.Id("k"), t = F.Id("t");
        Formula polynomial = Sub(F.D(1), Mul(new Formula.Fraction(Pow(k), F.D(2)), Pow(t)));
        return F.Disp(All("k", Reals, Call("IsLittleO", Call("nhds", F.D(0)),
            Lambda("t", Sub(Call("cos", Mul(k, t)), polynomial)), Lambda("t", Pow(t)))));
    }

    private static Formula TheoremFormula()
    {
        Formula f = F.Id("f"), k = F.Id("k"), t = F.Id("t");
        Formula bound = All("t", Reals,
            new Formula.Relation(new Formula.Absolute(At(f, t)),
                FormulaRelationOperator.LessThanOrEqual, F.D(1)));
        Formula duplication = All("t", Reals,
            Eq(At(f, Mul(F.D(2), t)), Sub(Mul(F.D(2), Pow(At(f, t))), F.D(1))));
        Formula polynomial = Sub(F.D(1), Mul(new Formula.Fraction(Pow(k), F.D(2)), Pow(t)));
        Formula germ = Call("IsLittleO", Call("nhds", F.D(0)),
            Lambda("t", Sub(At(f, t), polynomial)), Lambda("t", Pow(t)));
        Formula conclusion = All("t", Reals, Eq(At(f, t), Call("cos", Mul(k, t))));
        return F.Disp(All("f", F.Seq(Reals, F.To, F.Sp, Reals),
            All("k", Reals, Implies(bound, Implies(duplication, Implies(germ, conclusion))))));
    }
}
