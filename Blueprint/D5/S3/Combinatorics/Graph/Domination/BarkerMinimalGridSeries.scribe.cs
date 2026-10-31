using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class BarkerMinimalGridSeriesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/barker2017a286848");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete Barker series for actual minimal dominating subsets", H("The complete Barker series for actual minimal dominating subsets"), Blocks(
            N("lift", "lift", "A quotient integer vector is lifted to every full state by its literal class.", DescribeRole.Definition),
            N("intertwines", "intertwines", "For every quotient vector v, fullStep(lift v)=lift(step v). The proof applies the complete full-state successor permutation certificate and preserves every integer row multiplicity.", DescribeRole.Theorem),
            N("lift_orbit", "lift orbit", "For every natural k, fullOrbit k equals lift(orbit k). The initial terminal certificate and the linear intertwining supply induction on every k.", DescribeRole.Theorem),
            N("initial_sum", "initial sum", "For every quotient vector v, summing v at the classes of all 64 actual starts equals the sum of alpha(i)*v(i) over all 59 quotient classes.", DescribeRole.Theorem),
            N("numerator", "numerator", "The complete 49 integer coefficients of the source numerator include coefficient zero 0, coefficient one 2 and coefficient 48 −1. They reproduce Colin Barker, OEIS A286848, https://oeis.org/A286848, under CC-BY-SA-4.0, https://creativecommons.org/licenses/by-sa/4.0/.", DescribeRole.Definition),
            N("evaluate", "evaluate", "The integer linear functional evaluates a quotient vector against all 59 entries of the exact initial row alpha.", DescribeRole.Definition),
            N("quotientCoefficient", "quotientCoefficient", "The scalar coefficient is 0 at index zero, 2 at index one, and evaluation of orbit(n−2) thereafter. This is defined separately from the actual subset count.", DescribeRole.Definition),
            N("initialCoefficient", "initialCoefficient", "The initial range uses the exact certificate vectors values rather than assuming that they are powers.", DescribeRole.Definition),
            N("initial_convolutions", "initial convolutions", "Every convolution of the denominator with the initial coefficients in degrees zero through 49 equals the full literal numerator, with degree 49 zero.", DescribeRole.Theorem),
            N("all_later_convolutions", "all later convolutions", "For every m at least 50, the denominator convolution of quotientCoefficient at degree m is zero. Applying evaluate to shifted_annihilator(m−50) proves the entire unbounded range.", DescribeRole.Theorem),
            N("quotientSeries", "quotientSeries", "The rational formal power series has quotientCoefficient n cast to the rationals at each index n.", DescribeRole.Definition),
            N("P", "P", "The numerator formal polynomial series uses all literal numerator coefficients in degrees zero through 48 and is zero thereafter.", DescribeRole.Definition),
            N("Q", "Q", "The complete denominator is the finite sum of denominator(j) times X^j for every j in Fin 49. No leading or trailing coefficient is omitted.", DescribeRole.Definition),
            N("quotientSeries_mul_Q", "quotientSeries mul Q", "The product quotientSeries*Q equals P in rational formal power series. The proof separates the checked initial range zero through 49 from every later degree.", DescribeRole.Theorem),
            N("Q_constant", "Q constant", "The literal denominator has constant coefficient one.", DescribeRole.Theorem),
            N("quotientSeries_identity", "quotientSeries identity", "The quotient-orbit series equals P*Q inverse. This theorem alone does not identify the quotient coefficients with actual subset counts.", DescribeRole.Theorem),
            N("actualCount_quotient", "Every actual positive-width count", "For every natural k, the actual labelled inclusion-minimal dominating subset count of the open grid of width k+2, cast to the integers, equals evaluate(orbit k). The proof uses the all-length actual word count and the total partition certificates, with no assumed recurrence or count relation.", DescribeRole.Theorem),
            N("actualSeries", "The actual-subset series", "The rational formal power series has coefficient zero 0 and coefficient actualCount n at every positive n. The actual empty-grid count is not changed.", DescribeRole.Definition),
            N("whole_identity", "The entire Colin Barker identity", "actualSeries equals P times the inverse of Q in rational formal power series. P and Q contain every literal coefficient of Colin Barker's complete OEIS A286848 expression, including the leading x, both degree-48 terms, and denominator constant 1. All actual labelled inclusion-minimal dominating subsets are counted once for every width n at least 1.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a286848-barker-minimal-dominating-three-row-grids"),
                    ResolutionKind.Proved)),
            Paragraph(Text("The initial finite range and the shifted annihilator cover disjoint, exhaustive coefficient ranges. The denominator has constant term one, so its formal inverse exists over the rationals. Together with the actual-subset counting correspondence, this identifies every coefficient of the complete expression."))), []));

    private static DocumentBlock N(string name, string title, string prose, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("bs-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role, resolution);
}
