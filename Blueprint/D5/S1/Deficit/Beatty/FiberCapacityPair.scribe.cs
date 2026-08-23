using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit.Beatty;

internal sealed class FiberCapacityPairDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive golden first-coordinate fibers have capacity four or five, nonnegative dual fibers have capacity two or three, and each first-coordinate fiber has interval support in the second coordinate.",
        H("Capacity Pairs and Interval Support of Golden Fibers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-golden-fibers-are-finite"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Beatty/FiberCapacityPair.golden_fiber_finite"),
                H("Positive golden fibers are finite"),
                StatementSource.FromAuthor(PositiveFiberFiniteFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fixing a positive first coordinate leaves only finitely many word indices. "
                            + "Their second coordinates lie between two finite golden-ratio floor "
                            + "cutoffs, and each supported coordinate reconstructs one index."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("positive-golden-fibers-have-capacity-four-or-five"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Beatty/FiberCapacityPair.golden_fiber_capacity_pair"),
                H("Positive golden fibers have capacity four or five"),
                StatementSource.FromAuthor(PositiveFiberCapacityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every positive integer first-coordinate label, the corresponding "
                            + "golden fiber contains exactly four or exactly five indices.")),
                    Paragraph(Text(
                        "The two floor cutoffs for its second-coordinate support differ by three "
                            + "or four. Counting both endpoints of that integer interval gives the "
                            + "two possible fiber capacities."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonnegative-dual-fibers-have-capacity-two-or-three"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Beatty/FiberCapacityPair.golden_dual_fiber_capacity_pair"),
                H("Nonnegative dual fibers have capacity two or three"),
                StatementSource.FromAuthor(DualFiberCapacityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every nonnegative integer second-coordinate label, fixing that "
                            + "coordinate selects exactly two or exactly three natural indices.")),
                    Paragraph(Text(
                        "Successive ceiling cutoffs at the golden-ratio-square scale differ by "
                            + "two or three. The zero label is included and has capacity two."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("second-coordinate-support-is-a-closed-integer-interval"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Beatty/FiberCapacityPair.golden_fiber_b_support_eq_Icc"),
                H("Second-coordinate support is a closed integer interval"),
                StatementSource.FromAuthor(FiberSupportFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a positive first-coordinate label a, the second coordinates attained "
                            + "in its fiber are precisely all integers from floor((a - 1) phi) "
                            + "through floor((a + 1) phi), with both endpoints included.")),
                    Paragraph(Text(
                        "Every index in the fiber lands in this interval, and reconstructing an "
                            + "index from any integer in the interval realizes the reverse inclusion."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("second-coordinate-support-is-order-connected"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Beatty/FiberCapacityPair.golden_fiber_b_support_ordConnected"),
                H("Second-coordinate support is order connected"),
                StatementSource.FromAuthor(FiberSupportOrdConnectedFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Within a positive first-coordinate fiber, every integer lying between two "
                            + "attained second coordinates is also attained. This follows from the "
                            + "exact identification of the support with a closed integer interval."))),
                DescribeRole.Lemma))));

    private static Formula PositiveFiberFiniteFormula() => PositiveFirstCoordinateStatement(
        NamedCall(F.Id("Finite"), NamedCall(F.Id("goldenFiber"), F.Id("a"))));

    private static Formula PositiveFiberCapacityFormula() => PositiveFirstCoordinateStatement(
        Seq(
            NamedCall(F.Id("ncard"), NamedCall(F.Id("goldenFiber"), F.Id("a"))),
            Sp, InMacro, Sp, CapacitySet(D(4), D(5))));

    private static Formula DualFiberCapacityFormula() => Disp(Seq(
        Forall, Sp, F.Id("b"), Sp, InMacro, Sp, Integers(), Comma, Sp,
        D(0), Sp, Leq, Sp, F.Id("b"), Sp, Rightarrow, Sp,
        NamedCall(F.Id("ncard"), NamedCall(F.Id("goldenDualFiber"), F.Id("b"))),
        Sp, InMacro, Sp, CapacitySet(D(2), D(3))));

    private static Formula FiberSupportFormula() => PositiveFirstCoordinateStatement(Seq(
        FiberBImage(), Sp, Eq, Sp, FiberSupportInterval()));

    private static Formula FiberSupportOrdConnectedFormula() => PositiveFirstCoordinateStatement(
        NamedCall(F.Id("OrdConnected"), FiberBImage()));

    private static Formula PositiveFirstCoordinateStatement(Formula conclusion) => Disp(Seq(
        Forall, Sp, F.Id("a"), Sp, InMacro, Sp, Integers(), Comma, Sp,
        D(1), Sp, Leq, Sp, F.Id("a"), Sp, Rightarrow, Sp, conclusion));

    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));

    private static Formula Named(Formula identifier) => Seq(Operatorname, Grp(identifier));

    private static Formula NamedCall(Formula identifier, Formula argument) =>
        Seq(Named(identifier), Open, argument, Close);

    private static Formula FiberBImage() => Seq(
        Named(F.Id("fiberB")), OpenBracket,
        NamedCall(F.Id("goldenFiber"), F.Id("a")), CloseBracket);

    private static Formula FiberSupportInterval() => Seq(
        OpenBrace, Sp,
        F.Id("b"), Sp, InMacro, Sp, Integers(), Sp, Bar, Sp,
        NamedCall(F.Id("fiberSupportLower"), F.Id("a")), Sp, Leq, Sp, F.Id("b"),
        Sp, Land, Sp,
        F.Id("b"), Sp, Leq, Sp,
        NamedCall(F.Id("fiberSupportUpper"), F.Id("a")),
        Sp, CloseBrace);

    private static Formula CapacitySet(Formula first, Formula second) =>
        Seq(OpenBrace, Sp, first, Comma, Sp, second, Sp, CloseBrace);
}
