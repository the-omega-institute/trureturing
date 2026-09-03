using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Naming;

internal sealed class TestingCostClassificationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Naming/TestingCostClassification.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Testing-name code length filters, table execution cost does not, and mixed cost filters.",
        H("Testing Cost Classification"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fixed-support-execution-sublevel-is-infinite"),
                DeclarationHandle.Create(Prefix + "fixed_support_execution_sublevel_infinite"),
                H("A fixed-support-size execution sublevel is infinite"),
                StatementSource.FromAuthor(FixedSublevelFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Singleton supports embed the natural numbers into distinct finite-table "
                        + "names. Every such table has execution cost one, so execution cost alone "
                        + "cannot supply finite sublevels."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("testing-name-cost-classification"),
                DeclarationHandle.Create(Prefix + "testing_cost_classification"),
                H("Testing-name cost classification"),
                StatementSource.FromAuthor(ClassificationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The first clause applies the frozen testing-name code-length owner to an "
                            + "injective self-delimiting Boolean code.")),
                    Paragraph(Text(
                        "The second clause is the singleton-support counterfamily. The third "
                            + "observes that every mixed-cost sublevel lies inside the corresponding "
                            + "finite code-length sublevel."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/Naming/Conservation/TestingTowerMembership"))]));

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula NameType(Formula output) => Call("TestingName", output);

    private static Formula CostAt(Formula programCost, Formula name) =>
        Call("testingExecutionCost", programCost, name);

    private static Formula FixedSublevelFormula()
    {
        Formula output = F.Id("O");
        Formula value = F.Id("o0");
        Formula programCost = F.Id("programCost");
        Formula name = F.Id("a");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula bounded = new Formula.SetBuilder(
            Seq(CostAt(programCost, name), Sp, Leq, Sp, D(1)),
            name,
            NameType(output));

        return Disp(Seq(
            Forall, Sp, output, Colon, Sp, type, Comma, Sp,
            Forall, Sp, value, Colon, Sp, output, Comma, RowBreak, Grp(),
            Forall, Sp, programCost, Colon, Sp, Arrow(naturals, naturals), Comma, Sp,
            Call("Infinite", bounded), Dot));
    }

    private static Formula ClassificationFormula()
    {
        Formula output = F.Id("O");
        Formula value = F.Id("o0");
        Formula code = F.Id("code");
        Formula programCost = F.Id("programCost");
        Formula name = F.Id("a");
        Formula budget = F.Id("Q");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula names = NameType(output);
        Formula codeType = Arrow(names, Call("List", F.Id("Bool")));
        Formula programCostType = Arrow(naturals, naturals);
        Formula codeLength = Call("length", Call("code", name));
        Formula executionCost = CostAt(programCost, name);
        Formula finiteCode = Call("Finite", new Formula.SetBuilder(
            Seq(codeLength, Sp, Leq, Sp, budget), name, names));
        Formula infiniteExecution = Call("Infinite", new Formula.SetBuilder(
            Seq(executionCost, Sp, Leq, Sp, D(1)), name, names));
        Formula mixedCost = Seq(
            codeLength, Sp, Plus, Sp,
            Call("natLog", D(2), executionCost));
        Formula finiteMixed = Call("Finite", new Formula.SetBuilder(
            Seq(mixedCost, Sp, Leq, Sp, budget), name, names));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, output, Colon, Sp, type, Comma, Sp,
            Forall, Sp, value, Colon, Sp, output, Comma, RowBreak, Grp(),
            Forall, Sp, code, Colon, Sp, codeType, Comma, Sp,
            Forall, Sp, programCost, Colon, Sp, programCostType, Comma, RowBreak, Grp(),
            Call("Injective", code), Sp, Rightarrow, Sp, Open,
            Open, Forall, Sp, budget, Colon, Sp, naturals, Comma, Sp,
            finiteCode, Close, Sp, Land, RowBreak, Grp(),
            infiniteExecution, Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, budget, Colon, Sp, naturals, Comma, Sp,
            finiteMixed, Close, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
