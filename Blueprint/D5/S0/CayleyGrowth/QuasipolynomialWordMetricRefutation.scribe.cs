using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.CayleyGrowth;

internal sealed class QuasipolynomialWordMetricRefutationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Chervov2025 =
        LibraryNoteRef.Create("D5/L/CayleyGrowth/chervov2025cayleypy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A closed-form transposition family whose word metric is not eventually quasipolynomial.",
        H("Quasipolynomial Word Metric Refutation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("quasipolynomialwordmetricrefutation-square-indicator-obstruction"),
                DeclarationHandle.Create(
                    "D5/S0/CayleyGrowth/QuasipolynomialWordMetricRefutation."
                    + "not_eventuallyQuasipolynomial_of_eventually_squareIndicator"),
                H("The square indicator admits no eventual quasipolynomial"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A rational function of a natural argument is eventually quasipolynomial when some "
                    + "period admits one rational polynomial per residue class, agreeing with the function "
                    + "beyond some threshold; no degree bound is imposed. Suppose a function takes the value "
                    + "one at every perfect square and zero at every nonsquare, from some point on. Then it "
                    + "is not eventually quasipolynomial. Fix a period and look only at the residue class of "
                    + "zero. The squares of the multiples of the period lie in that class and are squares; "
                    + "adding the period to each of them gives numbers of the same class lying strictly "
                    + "between consecutive squares, hence nonsquares, because the period is at most twice "
                    + "the multiple. Shifting the index past both thresholds keeps both families infinite. "
                    + "The constituent polynomial of that one class therefore takes the value one on an "
                    + "infinite set and the value zero on another, so it equals both the constant one and "
                    + "the constant zero. The other constituents are never constrained."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quasipolynomialwordmetricrefutation-cayleypy-conjecture-two"),
                DeclarationHandle.Create(
                    "D5/S0/CayleyGrowth/QuasipolynomialWordMetricRefutation.cayleyPy_conjecture2_refuted"),
                H("Refutation of the marked-element growth conjecture"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Chervov2025),
                Blocks(Paragraph(Text(
                    "The literature note attests the conjecture, not this theorem. Take as generators every "
                    + "transposition of the finite type of size n, and as marked element the transposition of "
                    + "the first two indices when n is at least two and a perfect square, the identity "
                    + "otherwise. In the Cayley graph of that generating set the marked element is adjacent "
                    + "to the identity at square sizes, since a transposition is a generator and differs from "
                    + "the identity, and equal to the identity elsewhere. The distance from the identity is "
                    + "therefore one at squares of size at least two and zero at nonsquares, which is the "
                    + "square indicator. By the preceding theorem that distance is not eventually "
                    + "quasipolynomial of any degree, so in particular it is not given by a quadratic or "
                    + "linear quasipolynomial. Both objects are written by closed formulas and a square test, "
                    + "so the polynomial-time hypothesis of the conjecture holds of them; that hypothesis is "
                    + "discharged outside the formal statement."))),
                DescribeRole.Theorem))));
}
