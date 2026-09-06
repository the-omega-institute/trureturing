using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.DescriptionComplexity;

internal sealed class ThreeTowerCostSeparationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Computability/DescriptionComplexity/ThreeTowerCostSeparation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed-overhead compilers squeeze three affordable regions, while spikes and range tables witness two strict exponential cost gaps.",
        H("Three-Tower Cost Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("three-tower-cost-sandwich-and-double-separation"),
                DeclarationHandle.Create(
                    Prefix + "three_tower_cost_sandwich_and_double_separation"),
                H("Compiler inclusions give a distance sandwich and two strict separations"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A semantics-preserving prefix-to-test compiler with overhead c_PT and a "
                            + "test-to-program compiler with overhead c_TK embed the affordable "
                            + "regions at budgets B, B+c_PT, and B+c_PT+c_TK. The frozen nested-"
                            + "set distance theorem then reverses these inclusions into the stated "
                            + "infimum-distance sandwich.")),
                    Paragraph(Text(
                        "The nonemptiness premise on the prefix region is essential: real-valued "
                            + "infDist totalizes the empty-set case to zero. The source's unspecified "
                            + "additive constants are also made explicit as natural overheads and "
                            + "are accumulated in the two shifted budgets.")),
                    Paragraph(Text(
                        "For the first strict family, the spike at coordinate 2^j has indexed cost "
                            + "j+1, while every literal Boolean prefix denoting it has length at "
                            + "least 2^j+1. For the second, the literal table range(2^j) has cost "
                            + "2^j, while the program that computes the same range has cost j+1; "
                            + "this gap is strict for j at least two.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies List.getD_eq_default, Nat.log_pow, "
                            + "Nat.lt_two_pow_self, and Finset.card_range. The repository search "
                            + "found and directly reuses NameSetDistanceSandwich for the metric "
                            + "consequence; keyword, symbol-variant, digestion-state, generalized, "
                            + "and in-flight searches found neither strict separation family."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/Asymptotics/NameSetDistanceSandwich"))]));

    private static Formula TheoremFormula()
    {
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula prefix = F.Id("P"), testing = F.Id("T"), program = F.Id("K");
        Formula prefixOverhead = F.Id("cPT"), programOverhead = F.Id("cTK");
        Formula point = F.Id("x"), budget = F.Id("B"), index = F.Id("j");
        Formula bits = F.Id("bits");

        Formula affordable(Formula tower, Formula level) =>
            Call("Affordable", tower, level);
        Formula twoPower(Formula exponent) => Call("pow", D(2), exponent);
        Formula shiftedTestBudget = Seq(budget, Sp, Plus, Sp, prefixOverhead);
        Formula shiftedProgramBudget = Seq(
            budget, Sp, Plus, Sp, prefixOverhead, Sp, Plus, Sp, programOverhead);
        Formula prefixRegion = affordable(prefix, budget);
        Formula testRegion = affordable(testing, shiftedTestBudget);
        Formula programRegion = affordable(program, shiftedProgramBudget);
        Formula testDistance = Call("infDist", point, testRegion);
        Formula power = twoPower(index);
        Formula spike = Call("spike", power);
        Formula indexedCost = Call("indexedSpikeCost", power);
        Formula literalRange = Call("range", power);
        Formula rangeCost = Call("rangeProgramCost", power);
        Formula tableCost = Call("explicitTableCost", literalRange);

        Formula compilerPremises = Seq(
            Call("CostCompiler", prefix, testing, prefixOverhead), Sp, Land, Sp,
            Call("CostCompiler", testing, program, programOverhead), Sp, Land, Sp,
            Call("Nonempty", prefixRegion));
        Formula distanceSandwich = Seq(
            Call("infDist", point, programRegion), Sp, Leq, Sp, testDistance,
            Sp, Land, Sp, testDistance, Sp, Leq, Sp,
            Call("infDist", point, prefixRegion));
        Formula prefixLowerBound = Seq(
            Forall, Sp, bits, Comma, Sp,
            Call("prefixValue", bits), Sp, Eq, Sp, spike,
            Sp, Rightarrow, Sp, power, Sp, Plus, Sp, D(1), Sp, Leq, Sp,
            Call("length", bits));
        Formula spikeSeparation = Seq(
            Call("indexedSpikeValue", power), Sp, Eq, Sp, spike, Sp, Land, Sp,
            indexedCost, Sp, Eq, Sp, index, Sp, Plus, Sp, D(1), Sp, Land, Sp,
            indexedCost, Sp, Lt, Sp, power, Sp, Plus, Sp, D(1), Sp, Land, Sp,
            Open, prefixLowerBound, Close);
        Formula tableSeparation = Seq(
            Call("explicitTableValue", literalRange), Sp, Eq, Sp,
            Call("rangeProgramValue", power), Sp, Land, Sp,
            tableCost, Sp, Eq, Sp, power, Sp, Land, Sp,
            rangeCost, Sp, Eq, Sp, index, Sp, Plus, Sp, D(1), Sp, Land, Sp,
            rangeCost, Sp, Lt, Sp, tableCost);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, prefix, Comma, Sp, testing, Comma, Sp, program, Comma, Sp,
            prefixOverhead, Comma, Sp, programOverhead, Comma, Sp, point, Comma, Sp,
            budget, Comma, RowBreak, Grp(),
            compilerPremises, Sp, Rightarrow, Sp, RowBreak, Grp(),
            Open, distanceSandwich, Close, Sp, Land, Sp, RowBreak, Grp(),
            Open, Forall, Sp, index, InMacro, naturals, Comma, Sp,
            spikeSeparation, Close, Sp, Land, Sp, RowBreak, Grp(),
            Open, Forall, Sp, index, InMacro, naturals, Comma, Sp,
            index, Sp, Ge, Sp, D(2), Sp, Rightarrow, Sp,
            tableSeparation, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
