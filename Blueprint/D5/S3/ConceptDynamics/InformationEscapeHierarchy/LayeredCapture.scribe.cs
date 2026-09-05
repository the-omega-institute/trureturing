using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeHierarchy;

internal sealed class LayeredCaptureDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Certified kernel chains partition a finite arena into ordered captures and a final unresolved set.",
        H("Layered Capture"),
        Blocks(
            Definition("catalog-id", "CatalogId", "Catalog identity",
                "A catalog projection has a stable Lean name."),
            Definition("catalog-kind", "CatalogKind", "Catalog kind",
                "Catalogs are classified as canonical maximal families or bounded analysis views."),
            Definition("catalog-occurrence", "CatalogOccurrence", "Catalog occurrence",
                "An occurrence records root, catalog, arena, theorem, unit, realization, and theorem-unit identities."),
            Definition("maximal-catalog", "maximalCatalog", "Maximal catalog assembly",
                "Assembly retains the canonical occurrences matching one root and one object arena."),
            Definition("layer-chain", "LayerChain", "Certified layer chain",
                "Every adjacent kernel carries a proof that the later relation refines the earlier relation."),
            Definition("layered-capture-pairs", "layeredCapturePairs",
                "Layered capture pairs",
                "Layer zero contains pairs separated by the first kernel; successor layers contain pairs removed by one refinement."),
            Definition("layered-capture-count", "layeredCaptureCount",
                "Layered capture count", "The count is the cardinality of one layered capture set."),
            Definition("layered-capture-spectrum", "layeredCaptureSpectrum",
                "Layered capture spectrum", "The spectrum lists the capture count at every ordered layer."),
            Definition("layered-capture-rate", "layeredCaptureRate",
                "Layered capture rate",
                "Each exact rate divides its layer count by the arena's off-diagonal denominator."),
            Definition("unresolved-pairs", "unresolvedPairs", "Unresolved pairs",
                "The unresolved set contains off-diagonal pairs related by the final kernel."),
            Definition("unresolved-count", "unresolvedCount", "Unresolved count",
                "The unresolved count is the cardinality of the final unresolved set."),
            Definition("unresolved-rate", "unresolvedRate", "Unresolved rate",
                "The exact unresolved rate uses the same arena denominator as every layer."),
            Theorem("initial-layer-nonempty-criterion", "layeredCapture_zero_nonempty_iff",
                "Initial capture nonemptiness", InitialNonempty()),
            Theorem("successor-layer-nonempty-criterion",
                "layeredCapture_succ_nonempty_iff_strict",
                "Successor capture nonemptiness", SuccessorNonempty()),
            Theorem("layered-capture-partition", "layeredCapture_partition",
                "Layered capture partition", Partition()),
            Theorem("strict-refinement-is-nonempty-capture",
                "strictRefinement_iff_layeredCapture_nonempty",
                "Strict refinement is nonempty capture", StrictRefinement()),
            Theorem("cumulative-coarse-member-has-zero-unique-capture",
                "cumulativeChain_coarser_uniqueCapture_zero",
                "A finer peer zeros coarser unique capture", CoarserZero()),
            Definition("packed-catalog", "PackedCatalog", "Packed catalog",
                "A packed catalog stores an arena together with a catalog definitionally over that arena."),
            Definition("designated-root-catalog-suite", "DesignatedRootCatalogSuite",
                "Designated root catalog suite",
                "A finite dependent catalogAt family lists every maximal catalog owned by one sealing root."),
            Definition("system-catalog-irredundant", "SystemCatalogIrredundant",
                "System catalog irredundancy",
                "Every maximal catalog in the designated root must be irredundant."),
            Definition("system-wide-positive", "SystemWidePositive", "System-wide positivity",
                "The compatibility name denotes the same one-root universal proposition."),
            Theorem("system-wide-positive-iff-system-catalog-irredundant",
                "systemWidePositive_iff_systemCatalogIrredundant",
                "System positivity is designated-root irredundancy", SystemPositive()),
            Definition("schedule-to-layer-chain", "toLayerChain",
                "Generated schedule layer chain",
                "A classified generator schedule yields a certified general kernel chain."),
            Theorem("generated-layer-capture-is-schedule-increment",
                "toLayerChain_layeredCapture_succ_eq_increment",
                "Generated layered captures are schedule increments", ScheduleBridge()))));

    private static DocumentBlock.Describe Definition(
        string id, string declaration, string title, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Definition);

    private static DocumentBlock.Describe Theorem(
        string id, string declaration, string title, Formula formula) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(Seq(formula, Dot))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The certificate follows from the typed chain data and finite kernel-set algebra."))),
            DescribeRole.Theorem);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Chain() => F.Id("C");
    private static Formula Catalog() => F.Id("A");
    private static Formula Layer() => F.Id("r");
    private static Formula Index() => F.Id("i");
    private static Formula OtherIndex() => F.Id("j");
    private static Formula Left() => F.Id("x");
    private static Formula Right() => F.Id("y");
    private static Formula Captures(Formula layer) =>
        Call("layeredCapturePairs", Chain(), layer);
    private static Formula Kernel(Formula layer) => Call("kernel", Chain(), layer);
    private static Formula Relation(Formula kernel) =>
        Call("relation", kernel, Left(), Right());

    private static Formula InitialNonempty() => Seq(
        Call("Nonempty", Captures(Call("zero"))), Sp, Leftrightarrow, Sp,
        Exists, Sp, Left(), Comma, Sp, Right(), Comma, Sp,
        And(Seq(Left(), Sp, Neq, Sp, Right()),
            Seq(Neg, Relation(Kernel(Call("zero"))))));

    private static Formula SuccessorNonempty() => Seq(
        Call("Nonempty", Captures(Call("succ", Layer()))), Sp, Leftrightarrow, Sp,
        Exists, Sp, Left(), Comma, Sp, Right(), Comma, Sp,
        And(Relation(Kernel(Call("castSucc", Layer()))),
            Seq(Neg, Relation(Kernel(Call("succ", Layer()))))));

    private static Formula Partition()
    {
        Formula pairwise = Call("PairwiseDisjoint", Call("layers", Chain()));
        Formula unresolvedDisjoint =
            Call("DisjointFrom", Call("layers", Chain()), Call("unresolvedPairs", Chain()));
        Formula covers = Seq(
            Call("union", Call("biUnion", Call("layers", Chain())),
                Call("unresolvedPairs", Chain())),
            Sp, Eq, Sp, Call("offDiagonalPairs", Chain()));
        return And(pairwise, And(unresolvedDisjoint, covers));
    }

    private static Formula StrictRefinement() => Seq(
        Call("StrictSubset", Call("relation", Kernel(Call("succ", Layer()))),
            Call("relation", Kernel(Call("castSucc", Layer())))),
        Sp, Leftrightarrow, Sp,
        Call("Nonempty", Captures(Call("succ", Layer()))));

    private static Formula CoarserZero()
    {
        Formula premises = And(
            Seq(Index(), Sp, Neq, Sp, OtherIndex()),
            Call("KernelRefines", Catalog(), Index(), OtherIndex()));
        Formula conclusion = Seq(
            Call("uniqueCapturePairs", Catalog(), OtherIndex()),
            Sp, Eq, Sp, Emptyset);
        return Implies(premises, conclusion);
    }

    private static Formula SystemPositive() => Seq(
        Call("SystemWidePositive", F.Id("S")), Sp, Leftrightarrow, Sp,
        Call("SystemCatalogIrredundant", F.Id("S")));

    private static Formula ScheduleBridge() => Seq(
        Call("layeredCapturePairs", Call("toLayerChain", F.Id("G")),
            Call("succ", Layer())),
        Sp, Eq, Sp, Call("increment", F.Id("G"), Layer()));
}
