using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal;

internal sealed class QueryKernelHierarchyDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Causal/QueryKernelHierarchy.query_kernel_hierarchy";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nested observational, interventional, and counterfactual query families induce "
            + "a kernel chain, and both links admit concrete strictness witnesses.",
        H("Observation-Intervention-Counterfactual Query-Kernel Hierarchy"),
        Blocks(Describe.Lean(
            DescribeId.Create("query-kernel-hierarchy"),
            DeclarationHandle.Create(Declaration),
            H("Nested query families induce the kernel hierarchy"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Each observational answer is read from a designated interventional "
                        + "answer, and each interventional answer is read from a designated "
                        + "counterfactual answer. Equality at the richer layer therefore "
                        + "forces equality at the next layer.")),
                Paragraph(Text(
                    "The two final clauses reuse the established Boolean structural-model "
                        + "countermodels. One separates equal single-world intervention "
                        + "answers from cross-world responses; the other separates equal "
                        + "observations from intervention answers."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula type = TypeUniverse();
        Formula model = F.Id("M");
        Formula obsIndex = F.Id("ObsIndex");
        Formula intIndex = F.Id("IntIndex");
        Formula cfIndex = F.Id("CfIndex");
        Formula obsAnswer = F.Id("ObsAnswer");
        Formula intAnswer = F.Id("IntAnswer");
        Formula cfAnswer = F.Id("CfAnswer");
        Formula obsQuery = F.Id("obsQuery");
        Formula intQuery = F.Id("intQuery");
        Formula cfQuery = F.Id("cfQuery");
        Formula obsToInt = F.Id("obsToInt");
        Formula intToCf = F.Id("intToCf");
        Formula obsFromInt = F.Id("obsFromInt");
        Formula intFromCf = F.Id("intFromCf");
        Formula obsI = F.Id("oi");
        Formula intI = F.Id("ii");
        Formula first = F.Id("m");
        Formula second = F.Id("n");

        Formula obsContainment = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("oi", obsIndex), Bound("m", model)],
            Equal(
                Apply(
                    obsFromInt,
                    obsI,
                    Apply(intQuery, Apply(obsToInt, obsI), first)),
                Apply(obsQuery, obsI, first)));
        Formula intContainment = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("ii", intIndex), Bound("m", model)],
            Equal(
                Apply(
                    intFromCf,
                    intI,
                    Apply(cfQuery, Apply(intToCf, intI), first)),
                Apply(intQuery, intI, first)));

        Formula cfToInt = KernelInclusion(cfQuery, intQuery, model, first, second);
        Formula intToObs = KernelInclusion(intQuery, obsQuery, model, first, second);
        Formula cfStrictness = StrictnessWitness(F.Id("Int"), F.Id("CF"));
        Formula obsStrictness = StrictnessWitness(F.Id("Obs"), F.Id("Int"));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("M", type),
                Bound("ObsIndex", type),
                Bound("IntIndex", type),
                Bound("CfIndex", type),
                Bound("ObsAnswer", Arrow(obsIndex, type)),
                Bound("IntAnswer", Arrow(intIndex, type)),
                Bound("CfAnswer", Arrow(cfIndex, type)),
                Bound("obsQuery", DependentQueryType(obsIndex, model, obsAnswer, obsI)),
                Bound("intQuery", DependentQueryType(intIndex, model, intAnswer, intI)),
                Bound("cfQuery", DependentQueryType(cfIndex, model, cfAnswer, F.Id("ci"))),
                Bound("obsToInt", Arrow(obsIndex, intIndex)),
                Bound("intToCf", Arrow(intIndex, cfIndex)),
                Bound(
                    "obsFromInt",
                    DependentReadbackType(obsIndex, intAnswer, obsAnswer, obsToInt, obsI)),
                Bound(
                    "intFromCf",
                    DependentReadbackType(intIndex, cfAnswer, intAnswer, intToCf, intI)),
                Bound("hObs", obsContainment),
                Bound("hInt", intContainment),
            ],
            And(cfToInt, And(intToObs, And(cfStrictness, obsStrictness)))));
    }

    private static Formula KernelInclusion(
        Formula richer,
        Formula coarser,
        Formula model,
        Formula first,
        Formula second) =>
        new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("m", model), Bound("n", model)],
            Implies(
                Apply(F.Id("queryKernel"), richer, first, second),
                Apply(F.Id("queryKernel"), coarser, first, second)));

    private static Formula StrictnessWitness(Formula equalQuery, Formula distinctQuery)
    {
        Formula modelType = F.Id("DeterministicBoolSCM");
        Formula first = F.Id("S");
        Formula second = F.Id("T");

        return new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("S", modelType), Bound("T", modelType)],
            And(
                Equal(Apply(equalQuery, first), Apply(equalQuery, second)),
                NotEqual(Apply(distinctQuery, first), Apply(distinctQuery, second))));
    }

    private static Formula DependentQueryType(
        Formula indexType,
        Formula modelType,
        Formula answerFamily,
        Formula index) =>
        Seq(
            Open, Typed(index, indexType), Close, Sp, To, Sp,
            modelType, Sp, To, Sp, Apply(answerFamily, index));

    private static Formula DependentReadbackType(
        Formula indexType,
        Formula richAnswer,
        Formula coarseAnswer,
        Formula indexMap,
        Formula index) =>
        Seq(
            Open, Typed(index, indexType), Close, Sp, To, Sp,
            Apply(richAnswer, Apply(indexMap, index)), Sp, To, Sp,
            Apply(coarseAnswer, index));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }

            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Typed(Formula value, Formula domain) =>
        Seq(value, Colon, Sp, domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
}
