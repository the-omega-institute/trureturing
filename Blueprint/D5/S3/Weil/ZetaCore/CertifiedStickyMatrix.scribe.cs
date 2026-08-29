using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class CertifiedStickyMatrixDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A conservative finite lower form certifies Schur and full block positivity.",
        H("Certified Sticky Matrix"),
        Blocks(Describe.Lean(
            DescribeId.Create("certified-sticky-matrix"),
            DeclarationHandle.Create(
                "D5/S3/Weil/ZetaBridge/CertifiedStickyMatrix.certified_sticky_matrix"),
            H("Finite lower matrix certification"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "A positive complementary gap controls the coupling term. Positivity of "
                    + "the conservative lower form therefore implies Schur positivity, "
                    + "which implies positivity of the full block energy."))),
            DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Nonnegative(Formula value) =>
        new Formula.Relation(D(0), FormulaRelationOperator.LessThanOrEqual, value);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = And(clauses[index], result);
        return result;
    }

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type"), real = Call("Real");
        Formula hp = F.Id("HP"), hq = F.Id("HQ");
        Formula app = F.Id("APP"), aqp = F.Id("AQP");
        Formula aqq = F.Id("AQQ"), aqqInv = F.Id("AQQInv");
        Formula delta = F.Id("delta"), p = F.Id("p");
        Formula q = F.Id("q"), x = F.Id("x"), y = F.Id("y"), z = F.Id("z");
        Formula Map(Formula domain, Formula codomain) =>
            Call("LinearMap", real, domain, codomain);
        Formula Apply(Formula map, Formula value) => Call("apply", map, value);
        Formula Inner(Formula left, Formula right) => Call("inner", real, left, right);
        Formula SquaredNorm(Formula value) => Call("pow", Call("norm", value), D(2));

        Formula gap = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("q", hq)],
            new Formula.Relation(
                Call("mul", delta, SquaredNorm(q)),
                FormulaRelationOperator.LessThanOrEqual,
                Inner(Apply(aqq, q), q)));
        Formula symmetry = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("x", hq), Bound("y", hq)],
            Equal(Inner(Apply(aqq, x), y), Inner(x, Apply(aqq, y))));
        Formula conservative = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("p", hp)],
            Nonnegative(Call("sub", Inner(Apply(app, p), p),
                Call("mul", Call("inv", delta), SquaredNorm(Apply(aqp, p))))));
        Formula schurPositive = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("p", hp)],
            Nonnegative(Call("schurEnergy", app, aqp, aqq, aqqInv, p)));
        Formula blockPositive = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("z", Call("Prod", hp, hq))],
            Nonnegative(Call("blockEnergy", app, aqp, aqq, z)));
        Formula assumptions = All(
            Call("NormedAddCommGroup", hp),
            Call("InnerProductSpace", real, hp),
            Call("NormedAddCommGroup", hq),
            Call("InnerProductSpace", real, hq),
            Less(D(0), delta),
            gap,
            symmetry,
            Equal(Call("comp", aqq, aqqInv), Call("id", real, hq)));
        Formula conclusion = And(
            Implies(conservative, schurPositive),
            Implies(schurPositive, blockPositive));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("HP", type),
                Bound("HQ", type),
                Bound("APP", Map(hp, hp)),
                Bound("AQP", Map(hp, hq)),
                Bound("AQQ", Map(hq, hq)),
                Bound("AQQInv", Map(hq, hq)),
                Bound("delta", real),
            ],
            Implies(assumptions, conclusion)));
    }
}
