using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity;

internal sealed class GoldenSubshiftInvariantMeasureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cesaro averages of successive forward images of a point mass have a convergent "
            + "subsequence in the compact space of probability measures, and the telescoping "
            + "boundary term vanishes along it, so the limit is shift invariant.",
        H("An Invariant Measure on the Golden Word Subshift"),
        Blocks(
            Paragraph(Text(
                "Write X_g for the golden word subshift and sigma for its one-step forward "
                + "shift, which restricts to X_g because a shift of a subshift member is "
                + "again a member. For a point x of X_g, the Cesaro average A_{x,n} is the "
                + "normalized sum of the first n forward images of the Dirac mass at x; it "
                + "is a probability measure whenever n is positive. Below, BC(X_g) "
                + "denotes the bounded continuous real-valued functions on X_g. The "
                + "inverse n^{-1} is the total inverse of the reals, so it is zero at "
                + "n = 0; the identities below are stated for every natural n, and both "
                + "sides vanish in that degenerate case.")),
            Paragraph(Text(
                "Mathlib supplies the two analytic inputs: the space of probability measures "
                + "on a compact space is itself compact, and pushforward along a continuous "
                + "map is continuous for the topology of convergence in distribution. It "
                + "carries no existence theorem for invariant measures, so the construction "
                + "is carried out here for this system.")),
            Describe.Lean(
                DescribeId.Create("integral-of-cesaro-average"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/GoldenSubshiftInvariantMeasure."
                        + "integral_cesaroAverage"),
                H("Integrating a Cesaro average is averaging along the orbit"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("f"), InMacro, Sp, Operatorname,
                    Grp(F.Id("BC")), Open, F.Id("X"), Underscore, F.Id("g"), Close,
                    Comma, Sp, Forall, Sp, F.Id("x"), InMacro, Sp, F.Id("X"),
                    Underscore, F.Id("g"), Comma, Sp, Forall, Sp, F.Id("n"),
                    InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Int, Sp, F.Id("f"), Sp, F.Id("d"), F.Id("A"), Underscore,
                    Grp(Seq(F.Id("x"), Comma, F.Id("n"))), Sp, Eq, Sp,
                    F.Id("n"), Caret, Grp(Seq(Minus, D(1))), Sp,
                    Sum, Underscore, Grp(Seq(F.Id("k"), Sp, Lt, Sp, F.Id("n"))), Sp,
                    F.Id("f"), Open, SigmaLower, Caret, Grp(F.Id("k")), Open,
                    F.Id("x"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Integration against a finite sum of measures is the finite sum of the "
                    + "integrals, proved by induction on the block length; each summand is a "
                    + "pushed-forward Dirac mass, whose integral is one evaluation of f. The "
                    + "scalar normalization then produces the displayed average."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cesaro-shift-telescoping-difference"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/GoldenSubshiftInvariantMeasure."
                        + "cesaroAverage_shift_diff"),
                H("Shifting a Cesaro average leaves only a boundary term"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("f"), InMacro, Sp, Operatorname,
                    Grp(F.Id("BC")), Open, F.Id("X"), Underscore, F.Id("g"), Close,
                    Comma, Sp, Forall, Sp, F.Id("x"), InMacro, Sp, F.Id("X"),
                    Underscore, F.Id("g"), Comma, Sp, Forall, Sp, F.Id("n"),
                    InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Int, Sp, Open, F.Id("f"), Circ, SigmaLower, Close, Sp,
                    F.Id("d"), F.Id("A"), Underscore,
                    Grp(Seq(F.Id("x"), Comma, F.Id("n"))), Sp, Minus, Sp,
                    Int, Sp, F.Id("f"), Sp, F.Id("d"), F.Id("A"), Underscore,
                    Grp(Seq(F.Id("x"), Comma, F.Id("n"))), Sp, Eq, Sp,
                    F.Id("n"), Caret, Grp(Seq(Minus, D(1))), Open,
                    F.Id("f"), Open, SigmaLower, Caret, Grp(F.Id("n")), Open,
                    F.Id("x"), Close, Close, Sp, Minus, Sp, F.Id("f"), Open,
                    F.Id("x"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Applying the previous identity to f composed with sigma and to f, the "
                    + "two orbit sums differ by a telescoping cancellation of all interior "
                    + "terms. What survives is the difference of the two endpoint values, "
                    + "divided by the block length."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-subshift-invariant-probability-measure"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/GoldenSubshiftInvariantMeasure."
                        + "exists_invariant_probabilityMeasure"),
                H("The golden subshift carries an invariant probability measure"),
                StatementSource.FromAuthor(Disp(Seq(
                    Exists, Sp, Mu, Sp, InMacro, Sp, Operatorname,
                    Grp(F.Id("Prob")), Open, F.Id("X"), Underscore, F.Id("g"), Close,
                    Comma, Sp, Operatorname, Grp(F.Id("Measurable")), Open,
                    SigmaLower, Close, Sp, Land, Sp, Operatorname,
                    Grp(F.Id("map")), Open, SigmaLower, Close, Open, Mu, Close,
                    Sp, Eq, Sp, Mu))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Start from any point of X_g, which is nonempty because the golden word "
                    + "itself is a member. The averages A_{x,n+1} live in the space of "
                    + "probability measures on X_g, which is compact and sequentially "
                    + "compact because X_g is compact; take a convergent subsequence. "
                    + "Pushforward along sigma is continuous, so it carries that subsequence "
                    + "to a sequence converging to the pushforward of the limit. Along the "
                    + "subsequence the boundary term of the preceding identity is bounded by "
                    + "twice the supremum norm of f divided by the block length, hence tends "
                    + "to zero. The two limits therefore integrate every bounded continuous "
                    + "function alike, and finite Borel measures agreeing on all such "
                    + "integrals coincide. The conclusion is the two-part "
                    + "measure-preserving predicate: the shift is measurable, and the "
                    + "limit measure is its own pushforward. Uniqueness of the invariant "
                    + "measure is not claimed here, and no ergodicity statement is made."))),
                DescribeRole.Theorem))));
}
