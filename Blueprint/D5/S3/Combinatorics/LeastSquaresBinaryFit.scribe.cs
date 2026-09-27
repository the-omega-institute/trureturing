using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class LeastSquaresBinaryFitDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/LeastSquaresBinaryFit.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/wiseman2023a222955");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite sample is fitted best by a line of zero slope exactly when its position-weighted "
            + "total is balanced against its total, because completing the square in the slope and "
            + "the intercept leaves the centred cross term as the only obstruction.",
        H("Zero Slope Is Optimal Exactly When the Weighted Index Sum Is Balanced"),
        Blocks(
            Node("squared-error", "Squared error of an affine fit", "sqError", ErrorFormula(),
                "The sample is a list of rational values indexed from zero, read as the points "
                    + "whose abscissa is one more than the index. The squared error of an affine "
                    + "function is the sum over the sample of the square of the residual. Nothing "
                    + "restricts the values to two, so the object is a fit to an arbitrary finite "
                    + "rational sample.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("zero-slope-optimal", "Optimality of a line of zero slope", "ZeroSlopeOptimal",
                OptimalFormula(),
                "A line of zero slope is optimal when some constant function attains a squared "
                    + "error no larger than that of any affine function. Optimality is phrased as "
                    + "attainment rather than as uniqueness of the minimiser, which is what the "
                    + "source entry's convention on a single point requires: one point is "
                    + "fitted exactly by every line through it, and the entry declares that case "
                    + "to have zero slope.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("balanced-positions", "Balance of the weighted total",
                "BalancedPositions", BalancedFormula(),
                "Twice the position-weighted total equals the length plus one times the total. For "
                    + "a binary word this says the positions of the ones sum to the same value "
                    + "before and after reversal, since reversal sends a position to the length "
                    + "plus one minus that position; equivalently the average position of a one is "
                    + "the midpoint of the index range.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("the-conjectured-bridge", "The conjectured bridge", "claim", ClaimFormula(),
                "The source asserts that a binary word is counted by the entry precisely when it "
                    + "has the same sum of positions of ones as its reverse. The statement below "
                    + "carries no restriction to binary values, so the assertion about words is "
                    + "the instance in which every value is zero or one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("bridge-holds", "The bridge holds", "result", ResultFormula(),
                "Write the total, the position-weighted total, the mean value and the mean "
                    + "position; subtract the means to obtain the centred value and the centred "
                    + "position; and let the cross term be the sum of their products. For any "
                    + "intercept and slope, setting the shifted intercept to the mean value minus "
                    + "the intercept minus the slope times the mean position turns each residual "
                    + "into the centred value minus the slope times the centred position plus that "
                    + "shift. Expanding the square and summing, the two terms linear in the shift "
                    + "vanish because centred quantities sum to zero, leaving the squared error "
                    + "minus the centred total of squares equal to the slope squared times the "
                    + "sum of squared centred positions, plus the length times the shift squared, "
                    + "minus twice the slope times the cross term. When the cross term vanishes "
                    + "the remainder is a sum of two squares with nonnegative coefficients, so the "
                    + "mean with zero slope is optimal. When it does not vanish the length is at "
                    + "least two, so the sum of squared centred positions is positive, and taking "
                    + "the slope to be the cross term divided by it with zero shift makes the "
                    + "remainder negative, which no optimal line permits. At length one the "
                    + "centred position vanishes, so the cross term vanishes with it and both "
                    + "sides hold. The cross term equals the position-weighted total minus the "
                    + "mean position times the total, so its vanishing is the balance condition.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("least-squares-zero-slope-binary-words"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            resolution);

    private static Formula Range() =>
        Seq(Underscore, Grp(F.Id("i"), Eq, D(0)), Caret, Grp(F.Id("c"), Minus, D(1)));

    private static Formula Value() => Seq(F.Id("b"), Underscore, F.Id("i"));

    private static Formula Err(Formula a, Formula b) =>
        Seq(F.Id("E"), Open, F.Id("c"), Comma, Sp, F.Id("b"), Comma, Sp, a, Comma, Sp, b, Close);

    private static Formula ErrorFormula() =>
        Disp(Equal(Err(Alpha, Beta),
            Seq(Sum, Range(), Open, Value(), Minus, Alpha, Minus, Beta,
                Open, F.Id("i"), Plus, D(1), Close, Close, Caret, Grp(D(2)))));

    private static Formula OptimalFormula() =>
        Disp(Iff(Seq(F.Id("Z"), Open, F.Id("c"), Comma, Sp, F.Id("b"), Close),
            Seq(Exists, Sp, Alpha, Underscore, Grp(D(0)), Comma, Sp,
                Forall, Sp, Alpha, Comma, Sp, Forall, Sp, Beta, Comma, Sp,
                Err(Seq(Alpha, Underscore, Grp(D(0))), D(0)), Leq, Sp, Err(Alpha, Beta))));

    private static Formula BalancedFormula() =>
        Disp(Iff(Seq(F.Id("B"), Open, F.Id("c"), Comma, Sp, F.Id("b"), Close),
            Equal(Seq(D(2), Sum, Range(), Open, F.Id("i"), Plus, D(1), Close, Value()),
                Seq(Open, F.Id("c"), Plus, D(1), Close, Sum, Range(), Value()))));

    private static Formula Statement() =>
        Seq(Forall, Sp, F.Id("c"), Comma, Sp, Forall, Sp, F.Id("b"), Comma, Sp,
            Implication(Seq(D(0), Lt, Sp, F.Id("c")),
                Iff(Seq(F.Id("Z"), Open, F.Id("c"), Comma, Sp, F.Id("b"), Close),
                    Seq(F.Id("B"), Open, F.Id("c"), Comma, Sp, F.Id("b"), Close))));

    private static Formula ClaimFormula() => Disp(Iff(F.Id("claim"), Statement()));

    private static Formula ResultFormula() => Disp(Statement());

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Implication(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
}
