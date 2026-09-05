using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeRealizations;

internal sealed class UnifiedCausalMeasurementsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact reflected values measure the section 43.1 unified causal construction.",
        H("Unified Causal Measurements"),
        Blocks(
            Describe.Example(
                DescribeId.Create("unified-state-enumeration"),
                H("Unified state enumeration"),
                Seq(F.Id("unifiedStateEnumeration"), Colon, Sp,
                    Call("StateEnumeration", F.Id("unifiedArena"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A private duplicate-free list composes the landed sixteen-state IC and " +
                        "thirty-two-state OI enumerations for measurement only.")))),
            Measurement(
                "branch-local-escape-measurements",
                "Branch-local escape measurements",
                BranchLocalFormula(),
                "The literal cumulative readouts leave 80/20/0 ordered IC pairs and " +
                    "56/24/0 ordered OI pairs indistinguishable."),
            Measurement(
                "cumulative-causal-measurements",
                "Cumulative causal measurements",
                CumulativeFormula(),
                "The full counts are 2256/136/44/0, the layered captures are " +
                    "2120/92/44, and the flat unique counts are 0/0/44. The two zero " +
                    "results are the section 43.1 causal fixed-catalog instance of " +
                    "CIRPT-IE-024, not the general law owned by AnalysisLaws."))));

    private static DocumentBlock.Describe Measurement(
        string id, string title, Formula statement, string explanation) => Describe.Example(
            DescribeId.Create(id), H(title), statement, AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))));

    private static Formula Equality(Formula left, Formula right) =>
        Seq(left, Sp, Eq, Sp, right);

    private static Formula And(params Formula[] clauses)
    {
        var items = new List<Formula>();
        for (var index = 0; index < clauses.Length; index++)
        {
            if (index > 0) items.AddRange([Sp, Land, Sp]);
            items.Add(Seq(Open, clauses[index], Close));
        }
        return Seq([.. items]);
    }

    private static Formula ApplyExact(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Member(Formula owner, string member) =>
        Seq(owner, Dot, F.Id(member));

    private static Formula Card(Formula value) =>
        Member(value, "card");

    private static Formula EscapeCard(string branch, string readout) =>
        Card(ApplyExact(F.Id(branch), F.Id(readout)));

    private static Formula Full(string counts) =>
        Member(F.Id(counts), "full");

    private static Formula Unique(string index) =>
        ApplyExact(Member(F.Id("flatCumulativeCounts"), "unique"),
            Seq(Dot, F.Id(index)));

    private static Formula Subscripted(string name, string subscript) =>
        Seq(F.Id(name), Underscore, Grp(F.Id(subscript)));

    private static Formula BranchLocalFormula() => And(
        Equality(EscapeCard("icEscapePairs", "ObsU"), D(8, 0)),
        Equality(EscapeCard("icEscapePairs", "IntU"), D(2, 0)),
        Equality(EscapeCard("icEscapePairs", "CfU"), D(0)),
        Equality(EscapeCard("oiEscapePairs", "ObsU"), D(5, 6)),
        Equality(EscapeCard("oiEscapePairs", "IntU"), D(2, 4)),
        Equality(EscapeCard("oiEscapePairs", "CfU"), D(0)));

    private static Formula CumulativeFormula() => And(
        Equality(Full("emptyCumulativeCounts"), D(2, 2, 5, 6)),
        Equality(Full("observationCumulativeCounts"), D(1, 3, 6)),
        Equality(Full("interventionCumulativeCounts"), D(4, 4)),
        Equality(Full("counterfactualCumulativeCounts"), D(0)),
        Equality(Card(F.Id("unifiedOffDiagonalPairs")), D(2, 2, 5, 6)),
        Equality(Card(Subscripted("E", "obs")), D(1, 3, 6)),
        Equality(Card(Subscripted("E", "int")), D(4, 4)),
        Equality(Card(Subscripted("E", "cf")), D(0)),
        Equality(Card(Subscripted("L", "obs")), D(2, 1, 2, 0)),
        Equality(Card(Subscripted("L", "int")), D(9, 2)),
        Equality(Card(Subscripted("L", "cf")), D(4, 4)),
        Equality(Unique("observation"), D(0)),
        Equality(Unique("intervention"), D(0)),
        Equality(Unique("counterfactual"), D(4, 4)));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
}
