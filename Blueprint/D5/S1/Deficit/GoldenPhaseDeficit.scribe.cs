using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit;

internal sealed class GoldenPhaseDeficitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S1/Deficit/GoldenPhaseDeficit",
            "The golden Beatty deficit is classified exactly by two phase-sum thresholds."),
        H("Golden Phase Classification of the Beatty Deficit"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("golden-phase-classification-of-the-beatty-deficit"),
                H("Two phase thresholds determine all three deficit values"),
                LeanTheorem(
                    "D5/S1/Deficit/GoldenPhaseDeficit.golden_phase_deficit"),
                PhaseClassificationFormula(),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "For two natural indices, take the fractional parts of their shifted "
                        + "golden orbits and add them. The additive coboundary of the canonical "
                        + "golden Beatty shift equals plus one exactly below the inverse-golden "
                        + "threshold, equals minus one exactly at or above the golden-ratio "
                        + "threshold, and equals zero throughout the half-open band between "
                        + "those thresholds. Thus the phase sum determines the deficit value, "
                        + "which is strictly stronger than merely knowing that three values "
                        + "are possible.")),
                    Paragraph(Text(
                        "The proof is new glue over pinned Mathlib floor arithmetic. Expanding "
                        + "each real input into its integer floor and fractional part rewrites "
                        + "the Beatty coboundary as minus one minus the floor of the phase sum "
                        + "less the golden ratio. The standard bounds on fractional parts and "
                        + "the identity that the inverse golden ratio is the golden ratio less "
                        + "one then identify the floor as minus two, minus one, or zero on the "
                        + "three regions. Mathlib provides the component identities but no "
                        + "declaration with these two phase thresholds; the source atom's "
                        + "classification is therefore proved here rather than wrapped.")))
            )),
        []));

    private static Formula PhaseClassificationFormula() =>
        Disp(Seq(
            F.Id("c"), Open, F.Id("v"), Underscore, D(1), Comma, Sp, F.Id("v"),
            Underscore, D(2), Close, Eq, Plus, D(1), Sp, Leftrightarrow, Sp,
            F.Id("theta"), Open, F.Id("v"), Underscore, D(1), Close, Plus,
            F.Id("theta"), Open, F.Id("v"), Underscore, D(2), Close, Lt,
            Varphi, Caret, Grp(Minus, D(1)), Comma, Quad, Sp,
            F.Id("c"), Open, F.Id("v"), Underscore, D(1), Comma, Sp, F.Id("v"),
            Underscore, D(2), Close, Eq, Minus, D(1), Sp, Leftrightarrow, Sp,
            Varphi, Leq, Sp, F.Id("theta"), Open, F.Id("v"), Underscore, D(1), Close,
            Plus, F.Id("theta"), Open, F.Id("v"), Underscore, D(2), Close, Comma, Quad, Sp,
            F.Id("c"), Open, F.Id("v"), Underscore, D(1), Comma, Sp, F.Id("v"),
            Underscore, D(2), Close, Eq, D(0), Sp, Leftrightarrow, Sp,
            Varphi, Caret, Grp(Minus, D(1)), Leq, Sp,
            F.Id("theta"), Open, F.Id("v"), Underscore, D(1), Close, Plus,
            F.Id("theta"), Open, F.Id("v"), Underscore, D(2), Close, Lt, Varphi));
}
