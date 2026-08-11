using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation;

internal sealed class TestingDivergenceBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Estimation/TestingDivergenceBounds",
            "Divergence bounds make Le Cam's exact finite testing-error floor operational and expose the complementary regimes of Pinsker and Bretagnolle--Huber."),
        H("Divergence Bounds for Finite Two-Point Testing Error"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("bretagnolle-huber-remains-informative-after-pinsker-degenerates"),
                H("Bretagnolle--Huber remains informative after Pinsker degenerates"),
                LeanTheorem(
                    "D5/S3/Estimation/TestingDivergenceBounds.testing_error_bretagnolle_huber"),
                Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Forall, Sp, F.Id("A"), Colon, Sp,
                    Operatorname, Grp(F.Id("Finset")), Open, Iota, Close, Comma, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Eq, D(1),
                    Close, Sp, Land, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("q"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("q"), Open, F.Id("i"), Close, Eq, D(1),
                    Close, Sp, Land, RowBreak,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    F.Id("q"), Open, F.Id("i"), Close, Eq, D(0), Sp,
                    Rightarrow, Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Eq, D(0), Close,
                    Close, Sp, Rightarrow, Sp, RowBreak,
                    D(1), Minus,
                    Sqrt, Sp, Grp(
                        D(1), Minus,
                        Exp, Sp, Open, Minus,
                        F.Id("D"), Underscore,
                        Grp(Operatorname, Grp(F.Id("KL"))),
                        Open, F.Id("p"), Sp, Vert, Sp, F.Id("q"), Close,
                        Close),
                    Le, Sp,
                    Sum, Sp, Underscore,
                    Grp(F.Id("i"), InMacro, Sp, F.Id("A")), Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Plus,
                    Sum, Sp, Underscore,
                    Grp(
                        F.Id("i"), InMacro, Sp,
                        F.Id("A"), Caret, F.Id("c")), Sp,
                    F.Id("q"), Open, F.Id("i"), Close, Dot,
                    End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Waves 40 and 41 fixed the minimum over all finite two-point tests at " +
                        "exactly one minus total variation. That exact characterization " +
                        "is structural but is not generally a model-level quantity one can " +
                        "calculate directly. A divergence often is calculable, or admits a " +
                        "tractable model-specific upper bound. The present module therefore " +
                        "re-expresses the frozen testing floor in terms of relative entropy.")),
                    Paragraph(Text(
                        "The two bounds are chained corollaries, not new mathematics. Each is Le " +
                        "Cam's frozen bound composed with a frozen total-variation-versus-divergence " +
                        "inequality. The module consumes Pinsker and Bretagnolle--Huber; it does " +
                        "not re-derive either. The declaration testing_error_pinsker gives total " +
                        "error at least 1-sqrt(D/2), while testing_error_bretagnolle_huber gives " +
                        "total error at least 1-sqrt(1-exp(-D)). A downstream estimation argument " +
                        "can therefore use divergence directly.")),
                    Paragraph(Text(
                        "Their assumptions are exactly the union required by the frozen inputs. " +
                        "Le Cam requires equal total mass and unit mass. Pinsker and " +
                        "Bretagnolle--Huber additionally require pointwise nonnegativity of both " +
                        "laws and the discrete absolute-continuity convention q(i)=0 implies " +
                        "p(i)=0. Apart from the finite carrier and the supplied test event, the " +
                        "composed statements add no hypothesis of their own. The composition is " +
                        "therefore tight at the level of assumptions rather than lossy.")),
                    Paragraph(Text(
                        "The comparison is the module's central result. The theorem " +
                        "pinsker_floor_nonpos_of_two_le proves, for every real D at least two, " +
                        "that the Pinsker-form floor 1-sqrt(D/2) is nonpositive. It is exactly zero " +
                        "at D=2 and decreases thereafter; at D=10 it is approximately -1.24. " +
                        "Such a right side says nothing: total testing error is a sum of masses " +
                        "and is already bounded below by zero.")),
                    Paragraph(Text(
                        "The theorem bretagnolle_huber_floor_pos proves the contrasting fact for " +
                        "every real D, without restricting D to be nonnegative: the floor " +
                        "1-sqrt(1-exp(-D)) is strictly positive. At D=2 it is approximately " +
                        "0.0701, and at D=10 it is approximately 2.27e-5. The latter value is " +
                        "small but remains strictly positive, so the Bretagnolle--Huber form " +
                        "never degenerates at any finite real argument.")),
                    Paragraph(Text(
                        "This is the estimation-side payoff of proving Bretagnolle--Huber four " +
                        "waves after Pinsker. Pinsker is sharper when the laws are close; only " +
                        "Bretagnolle--Huber continues to say something when they are far apart. " +
                        "The two inequalities are complementary in precisely the sense claimed " +
                        "by the Bretagnolle--Huber wave, and the present module makes that claim " +
                        "operational for testing error rather than leaving it as a comparison of " +
                        "total-variation upper bounds.")),
                    Paragraph(Text(
                        "The proof architecture contains no hidden analytic step. Each testing " +
                        "theorem first substitutes its frozen total-variation upper bound into " +
                        "one minus total variation and then applies Le Cam's frozen total-error " +
                        "bound to the supplied event. The two scalar comparison theorems isolate " +
                        "the operational difference: elementary square-root monotonicity makes " +
                        "the Pinsker floor nonpositive from two onward, while positivity of the " +
                        "exponential keeps the Bretagnolle--Huber square root strictly below one.")),
                    Paragraph(Text(
                        "No minimax or sample-complexity corollary, multi-point generalization, " +
                        "measure-theoretic analogue, or theorem deciding which bound is sharper " +
                        "throughout the intermediate regime is claimed. Beyond the two proved " +
                        "floor facts, no crossover point is asserted. Relative entropy uses the " +
                        "natural logarithm, so all divergence values in these statements are in " +
                        "nats.")))))));
}
