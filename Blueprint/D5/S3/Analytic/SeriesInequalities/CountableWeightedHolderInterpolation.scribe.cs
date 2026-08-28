using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SeriesInequalities;

internal sealed class CountableWeightedHolderInterpolationDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonnegative summable families obey weighted geometric-mean interpolation.",
        H("Countable Weighted Holder Interpolation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("countable-weighted-holder-interpolation"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/SeriesInequalities/"
                    + "CountableWeightedHolderInterpolation."
                    + "countable_weighted_holder_interpolation"),
                H("A weighted geometric-mean series is bounded by its endpoint sums"),
                StatementSource.FromAuthor(InterpolationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let f and g be nonnegative summable real families on an arbitrary "
                        + "index type, and let a and b be positive weights with a+b=1. The "
                        + "sum of f(i)^a g(i)^b is at most the product of the endpoint sums "
                        + "raised to a and b.")),
                    Paragraph(Text(
                        "The proof applies countable Holder inequality with conjugate "
                        + "exponents 1/a and 1/b. Raising f(i)^a to 1/a recovers f(i), and "
                        + "the same cancellation recovers g(i), including when a term is "
                        + "zero because both weights are positive.")),
                    Paragraph(Text(
                        "This theorem packages the common interpolation step used by the "
                        + "golden displacement log-convexity argument. Two earlier private "
                        + "specializations in the frozen zeta modules demonstrate the same "
                        + "need but remain unchanged.")),
                    Paragraph(Text(
                        "The theorem does not assert equality conditions, strictness, signed "
                        + "or complex variants, nonsummable endpoint behavior, zero endpoint "
                        + "weights, or interpolation among more than two families."))),
                DescribeRole.Theorem))));

    private static Formula InterpolationFormula()
    {
        Formula i = F.Id("i");
        Formula f = F.Id("f");
        Formula g = F.Id("g");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula fi = Apply(f, i);
        Formula gi = Apply(g, i);
        Formula leftTerm = F.Seq(
            fi, F.Caret, F.Grp(a), F.Sp, F.Cdot, F.Sp,
            gi, F.Caret, F.Grp(b));
        Formula left = Tsum(i, leftTerm);
        Formula right = F.Seq(
            F.Grp(Tsum(i, fi)), F.Caret, F.Grp(a), F.Sp, F.Cdot, F.Sp,
            F.Grp(Tsum(i, gi)), F.Caret, F.Grp(b));

        return F.Disp(F.Seq(
            F.Begin, F.Grp(F.Id("gathered")),
            F.Forall, F.Sp, F.Id("iota"), F.Comma, F.RowBreak,
            F.Forall, F.Sp, f, F.Comma, F.Sp, g, F.Colon, F.Sp,
            F.Id("iota"), F.To, F.Sp, F.Mathbb, F.Grp(F.Id("R")), F.Comma, F.RowBreak,
            Nonnegative(f), F.Sp, F.Land, F.Sp, Nonnegative(g), F.Sp, F.Land, F.RowBreak,
            Summable(f), F.Sp, F.Land, F.Sp, Summable(g), F.Sp, F.Land, F.RowBreak,
            F.D(0), F.Lt, F.Sp, a, F.Sp, F.Land, F.Sp,
            F.D(0), F.Lt, F.Sp, b, F.Sp, F.Land, F.Sp,
            a, F.Plus, b, F.Eq, F.D(1), F.Sp, F.Rightarrow, F.RowBreak,
            left, F.Sp, F.Le, F.Sp, right, F.Dot,
            F.End, F.Grp(F.Id("gathered"))));
    }

    private static Formula Nonnegative(Formula family) => F.Seq(
        F.Open, F.Forall, F.Sp, F.Id("i"), F.Comma, F.Sp,
        F.D(0), F.Le, F.Sp, Apply(family, F.Id("i")), F.Close);

    private static Formula Summable(Formula family) =>
        Apply(F.Id("Summable"), family);

    private static Formula Tsum(Formula index, Formula body) => F.Seq(
        F.Sum, F.Underscore, F.Grp(index), F.Sp, body);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
}
