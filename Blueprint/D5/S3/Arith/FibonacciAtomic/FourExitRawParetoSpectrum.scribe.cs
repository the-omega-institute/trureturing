using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class FourExitRawParetoSpectrumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The raw four-exit family has a complete menu of simultaneously attainable minimal excess vectors.",
        H("Four-Exit Raw Pareto Spectrum"),
        Blocks(Describe.Lean(
            DescribeId.Create("four-exit-raw-pareto-spectrum"),
            DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/FourExitRawParetoSpectrum.result"),
            H("The complete actual endpoint menu"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For every positive integer k, the literal right-comb family contains a baseline "
                + "and four exceptional rows A, Y, H, Z at each of k slots. Every row has "
                + "8k + 16 compulsory leaves. Costs count the distinct addresses actually requested "
                + "by a deterministic strategy that terminates and correctly decides membership "
                + "in the third substitution image on every finite input tree.")),
                Paragraph(Text(
                "The endpoint menu has two kinds of vectors. A first-kind vector is zero at "
                + "the baseline or at a single Y, H, or Z row, and one elsewhere. A second-kind "
                + "vector is zero at an A row, two at one of the Y, H, Z rows in that same slot, "
                + "and one elsewhere. Every correct strategy has cost at least the compulsory "
                + "leaf count plus one menu vector in every coordinate. Conversely, each menu "
                + "vector is the exact excess of a single correct strategy simultaneously on "
                + "all 4k + 1 rows. The coordinatewise minimal actual excess vectors are exactly "
                + "the menu, whose cardinality is 6k + 1. No assertion is made that every vector "
                + "above this menu is attainable.")),
                Paragraph(Text(
                "The baseline endpoint uses ordinary scans at all slots. The other endpoints "
                + "use one of six local five-row recipes, transported to the selected slot's "
                + "coordinates and extended by ordinary scans at the remaining slots. Actual "
                + "joint-response realization supplies a correct strategy with those simultaneous "
                + "costs. Each endpoint has a unique zero coordinate; endpoints sharing an A zero "
                + "differ in the location of their two. Thus the menu is an antichain. Domination "
                + "and attainment identify all minimal actual vectors, and the two endpoint "
                + "kinds contribute 3k + 1 and 3k distinct vectors."))),
            DescribeRole.Theorem))));
}
