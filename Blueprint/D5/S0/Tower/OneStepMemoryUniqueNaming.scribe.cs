using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower;

internal sealed class OneStepMemoryUniqueNamingDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S0/Tower/OneStepMemoryUniqueNaming.one_step_memory_unique_naming";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gapless unique weighting of one-step binary names forces Fibonacci weights and growth.",
        H("One-Step Memory Unique Naming"),
        Blocks(Describe.Lean(
            DescribeId.Create("one-step-memory-unique-naming"),
            DeclarationHandle.Create(Declaration),
            H("Unique seamless one-step naming forces Fibonacci growth"),
            StatementSource.FromAuthor(Formula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "GoldenName(n) is the canonical carrier of length-n binary words with no "
                        + "adjacent occupied positions. The weight function is indexed by its "
                        + "canonical Fibonacci indices, so source weight a_m is weight(m+1).")),
                Paragraph(Text(
                    "The hypothesis says that the actual weighted-sum map is bijective from "
                        + "the whole canonical name layer onto the initial interval below B(n). "
                        + "It therefore includes both uniqueness and gapless coverage.")),
                Paragraph(Text(
                    "Layer cardinality first forces B(n)=Fib(n+2). Comparing the old layer with "
                        + "the new singleton at index n+2 then forces its weight to equal B(n). "
                        + "The pinned Fibonacci ratio limit supplies the final golden growth rate."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Tower/GoldenNames")),
        ]));

    private static Formula Formula()
    {
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula sequenceType = new Formula.TypeArrow(naturals, naturals);
        Formula weight = F.Id("weight");
        Formula counts = F.Id("B");
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula name = F.Id("name");
        Formula value = F.Id("v");
        Formula nPlusTwo = Seq(n, Sp, Plus, Sp, D(2));
        Formula nameLayer = Call("GoldenName", n);
        Formula weightedSum = Seq(
            Sum, Underscore, Grp(k, Sp, InMacro, Sp, name), Sp,
            new Formula.Apply(weight, [k]));
        Formula weightedMap = Seq(
            Open, name, Colon, Sp, nameLayer, Sp, Mapsto, Sp, weightedSum, Close);
        Formula targetInterval = new Formula.SetBuilder(
            Seq(value, Sp, Lt, Sp, new Formula.Apply(counts, [n])), value, naturals);
        Formula exactCover = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            naturals,
            Call("BijOn", weightedMap, Call("univ", nameLayer), targetInterval));
        Formula forcedWeights = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            naturals,
            Equal(new Formula.Apply(weight, [nPlusTwo]), Call("Fib", nPlusTwo)));
        Formula forcedCounts = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            naturals,
            Equal(new Formula.Apply(counts, [n]), Call("Fib", nPlusTwo)));
        Formula growthFunction = Seq(
            Open, n, Colon, Sp, naturals, Sp, Mapsto, Sp,
            Frac,
            Grp(Open, new Formula.Apply(counts, [Seq(n, Sp, Plus, Sp, D(1))]),
                Sp, Colon, Sp, reals, Close),
            Grp(Open, new Formula.Apply(counts, [n]), Sp, Colon, Sp, reals, Close),
            Close);
        Formula growth = Call(
            "Tendsto", growthFunction, F.Id("atTop"), Call("nhds", Varphi));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, weight, Comma, Sp, counts, Colon, Sp, sequenceType,
            Comma, RowBreak, Grp(),
            exactCover, Sp, Rightarrow, RowBreak, Grp(),
            forcedWeights, Sp, Land, RowBreak, Grp(),
            forcedCounts, Sp, Land, RowBreak, Grp(),
            growth, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
