using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaLinear;

internal sealed class ExactStickyReductionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Completing a positive complementary block preserves positivity and negative inertia.",
        H("Exact Sticky Reduction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exact-sticky-reduction"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/ZetaLinear/ExactStickyReduction.exact_sticky_reduction"),
                H("Exact sticky reduction"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let HP and HQ be real inner-product spaces representing the retained "
                            + "and complementary summands. The full block energy and its Schur "
                            + "energy are constructed from APP, AQP, AQQ, and a right inverse "
                            + "of AQQ.")),
                    Paragraph(Text(
                        "Assume the complementary block is nonnegative and symmetric. Then the "
                            + "full energy is nonnegative exactly when the Schur energy is, and "
                            + "their negative inertia indices agree.")),
                    Paragraph(Text(
                        "The negative index is the supremum of dimensions of finite negative-"
                            + "definite subspaces, so the statement remains meaningful when HQ "
                            + "is infinite-dimensional. The proof completes the square and "
                            + "transports every finite negative subspace in both directions."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Nonnegative(Formula value) =>
        new Formula.Relation(D(0), FormulaRelationOperator.LessThanOrEqual, value);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula TheoremFormula()
    {
        Formula type = Call("Type");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula hp = F.Id("HP");
        Formula hq = F.Id("HQ");
        Formula app = F.Id("APP");
        Formula aqp = F.Id("AQP");
        Formula aqq = F.Id("AQQ");
        Formula aqqInv = F.Id("AQQInv");
        Formula Map(Formula domain, Formula codomain) =>
            Call("LinearMap", real, domain, codomain);

        Formula q = F.Id("q");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula z = F.Id("z");
        Formula p = F.Id("p");
        Formula block = Call("blockEnergy", app, aqp, aqq);
        Formula schur = Call("schurEnergy", app, aqp, aqq, aqqInv);

        Formula qqNonnegative = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("q", hq)],
            Nonnegative(Call("inner", Call("apply", aqq, q), q)));
        Formula qqSymmetric = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("x", hq), Bound("y", hq)],
            Equal(
                Call("inner", Call("apply", aqq, x), y),
                Call("inner", x, Call("apply", aqq, y))));
        Formula assumptions = And(
            Call("NormedAddCommGroup", hp),
            And(
                Call("InnerProductSpace", real, hp),
                And(
                    Call("NormedAddCommGroup", hq),
                    And(
                        Call("InnerProductSpace", real, hq),
                        And(
                            qqNonnegative,
                            And(
                                qqSymmetric,
                                Equal(
                                    Call("comp", aqq, aqqInv),
                                    Call("id", real, hq))))))));

        Formula blockNonnegative = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("z", Call("Prod", hp, hq))],
            Nonnegative(Call("apply", block, z)));
        Formula schurNonnegative = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("p", hp)],
            Nonnegative(Call("apply", schur, p)));
        Formula positivity = new Formula.Logic(
            blockNonnegative,
            FormulaLogicOperator.Iff,
            schurNonnegative);
        Formula inertia = Equal(
            Call("negativeIndex", block),
            Call("negativeIndex", schur));

        return new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("HP", type),
                Bound("HQ", type),
                Bound("APP", Map(hp, hp)),
                Bound("AQP", Map(hp, hq)),
                Bound("AQQ", Map(hq, hq)),
                Bound("AQQInv", Map(hq, hq)),
            ],
            Implies(assumptions, And(positivity, inertia)));
    }
}
