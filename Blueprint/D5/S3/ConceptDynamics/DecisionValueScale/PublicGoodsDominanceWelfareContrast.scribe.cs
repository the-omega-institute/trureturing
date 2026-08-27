using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DecisionValueScale;

internal sealed class PublicGoodsDominanceWelfareContrastDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/DecisionValueScale/PublicGoodsDominanceWelfareContrast."
            + "public_goods_dominance_welfare_contrast";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Private noncontribution dominance contrasts with maximal unanimous-contribution welfare.",
        H("Public Goods Dominance-Welfare Contrast"),
        Blocks(Describe.Lean(
            DescribeId.Create("public-goods-dominance-welfare-contrast"),
            DeclarationHandle.Create(Declaration),
            H("Private incentives and social welfare point in opposite directions"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The imported contribution level, aggregate, and zero-compensation utility "
                        + "construct the source payoff. Changing one agent's action to contribution "
                        + "changes that payoff by b/n-c, independently of the other actions.")),
                Paragraph(Text(
                    "Summing the same individual utilities counts every contribution benefit n "
                        + "times and its private cost once. The resulting welfare coefficient b-c "
                        + "is positive, so unanimous contribution is socially maximal even though "
                        + "noncontribution is privately strictly dominant."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/ConceptDynamics/DecisionValue/ContributionIncentiveThreshold")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula nat = F.Id("Nat");
        Formula real = F.Id("Real");
        Formula boolean = F.Id("Bool");
        Formula agents = F.Id("n");
        Formula benefit = F.Id("b");
        Formula cost = F.Id("c");
        Formula agent = F.Id("i");
        Formula other = F.Id("j");
        Formula profile = F.Id("a");
        Formula agentType = Call("Fin", agents);
        Formula profileType = Arrow(agentType, boolean);
        Formula allFalse = Call("const", D(0));
        Formula allTrue = Call("const", D(1));

        Formula ActionAt(Formula actions, Formula index) =>
            new Formula.Subscript(actions, index);
        Formula LevelAt(Formula actions, Formula index) =>
            Call("level", ActionAt(actions, index));
        Formula UtilityAt(Formula actions, Formula index) =>
            Call("u", index, actions);
        Formula WelfareAt(Formula actions) => Call("W", actions);
        Formula ContributionSum(Formula actions) => Call(
            "sum",
            other,
            agentType,
            LevelAt(actions, other));

        Formula utilityDefinition = Seq(
            Operatorname,
            Grp(F.Id("let")),
            Sp,
            UtilityAt(profile, agent),
            Sp,
            Colon,
            Eq,
            Sp,
            new Formula.Fraction(benefit, agents),
            Sp,
            Times,
            Sp,
            ContributionSum(profile),
            Sp,
            Minus,
            Sp,
            cost,
            Sp,
            Times,
            Sp,
            LevelAt(profile, agent),
            Semi,
            Sp);
        Formula welfareDefinition = Seq(
            Operatorname,
            Grp(F.Id("let")),
            Sp,
            WelfareAt(profile),
            Sp,
            Colon,
            Eq,
            Sp,
            Call("sum", agent, agentType, UtilityAt(profile, agent)),
            Semi,
            Sp);

        Formula privateDominance = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", agentType), Bound("a", profileType)],
            LessThan(
                UtilityAt(Call("update", profile, agent, D(1)), agent),
                UtilityAt(Call("update", profile, agent, D(0)), agent)));
        Formula welfareIdentity = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("a"),
            profileType,
            Equal(
                WelfareAt(profile),
                Seq(
                    Open,
                    benefit,
                    Sp,
                    Minus,
                    Sp,
                    cost,
                    Close,
                    Sp,
                    Times,
                    Sp,
                    ContributionSum(profile))));
        Formula welfareMaximum = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("a"),
            profileType,
            LessOrEqual(WelfareAt(profile), WelfareAt(allTrue)));
        Formula strictContrast = LessThan(WelfareAt(allFalse), WelfareAt(allTrue));
        Formula conclusion = And(
            privateDominance,
            And(welfareIdentity, And(welfareMaximum, strictContrast)));
        Formula premises = And(
            LessOrEqual(D(2), agents),
            And(
                LessThan(cost, benefit),
                LessThan(new Formula.Fraction(benefit, agents), cost)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("n", nat),
                Bound("b", real),
                Bound("c", real),
            ],
            Implies(
                premises,
                Seq(utilityDefinition, welfareDefinition, conclusion))));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
}
