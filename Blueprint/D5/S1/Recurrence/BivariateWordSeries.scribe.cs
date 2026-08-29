using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class BivariateWordSeriesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Admissible-word bookkeeping obeys its bivariate self-substitution equation.",
H("The Bivariate Admissible-Word Equation"),
Blocks(
            Describe.Lean(
                DescribeId.Create("bivariate-admissible-word-self-equation"),
                DeclarationHandle.Create("D5/S1/Recurrence/BivariateWordSeries.bookkeeping_series_self_functional_equation"),
                H("The word series splits into its two substituted branches"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, Operatorname, Grp(F.Id("bookkeepingSeries")), Colon, Sp,
                    Operatorname, Grp(F.Id("Degree")), Sp, To, Sp,
                    Operatorname, Grp(F.Id("Cardinal")), Close,
                    Sp, Eq, Sp, Open,
                    F.Id("degree"), Colon, Sp, Operatorname, Grp(F.Id("Degree")),
                    Sp, Mapsto, Sp,
                    Operatorname, Grp(F.Id("skipBranchSeries")),
                    Open, F.Id("degree"), Close, Sp, Plus, Sp,
                    Operatorname, Grp(F.Id("takeBranchSeries")),
                    Open, F.Id("degree"), Close, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The coefficients count finite binary words with no adjacent occupied "
                        + "positions by a pair of bookkeeping exponents. A canonical nonempty "
                        + "word is either a single occupied position, a skipped position followed "
                        + "by a nonempty word, or an occupied position followed by a forced skip "
                        + "and a nonempty word. Including the empty word makes this a disjoint "
                        + "two-branch decomposition.")),
                    Paragraph(Text(
                        "Skipping the lowest position sends an exponent pair (a, b) to "
                        + "(b, a+b), which is the monomial substitution (u, v) to (v, uv). "
                        + "Occupying it sends (a, b) to (a+b+1, a+2b), which is multiplication "
                        + "by u after the substitution (u, v) to (uv, uv^2). The Lean proof "
                        + "constructs an explicit equivalence on every coefficient fiber and "
                        + "uses pinned Mathlib's cardinality-of-equivalence and cardinality-of-sum "
                        + "declarations. Mathlib supplies that general machinery but has no "
                        + "declaration for this admissible-word equation, so the combinatorial "
                        + "bijection is new proof content rather than a wrapper."))),
                DescribeRole.Theorem))));
}
