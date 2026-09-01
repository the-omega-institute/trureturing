using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity;

internal sealed class GoldenSubshiftInvariantSupportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every shift-invariant Borel probability measure on the golden word subshift has "
            + "full support and is therefore positive on every nonempty open set.",
        H("Invariant Measures Have Full Support"),
        Blocks(
            Paragraph(Text(
                "Write X_g for the golden word subshift, sigma for its one-step forward "
                + "shift, and supp(mu) for the support of a measure mu. Mathlib proves that "
                + "positivity on every nonempty open set implies full support. The result "
                + "below supplies the converse needed here: if every point lies in "
                + "the support, then any nonempty open set is a neighbourhood of one of "
                + "those points and consequently has positive measure.")),
            Describe.Lean(
                DescribeId.Create("open-positive-from-full-support"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/GoldenSubshiftInvariantSupport."
                        + "isOpenPosMeasure_of_support_eq_univ"),
                H("Full support makes every nonempty open set positive"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, Mu, Sp, InMacro, Sp, Operatorname,
                    Grp(F.Id("Measure")), Open, F.Id("X"), Underscore, F.Id("g"), Close,
                    Comma, Sp, Operatorname, Grp(F.Id("supp")), Open, Mu, Close, Sp, Eq,
                    Sp, F.Id("X"), Underscore, F.Id("g"), Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("IsOpenPosMeasure")), Open, Mu, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Choose a point in a nonempty open set. Full support puts that point in "
                    + "the support, whose neighbourhood characterization says that every "
                    + "neighbourhood of the point has nonzero measure. Applied to the given "
                    + "open set, this is precisely positivity on nonempty open sets."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("support-preserved-by-invariant-shift"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/GoldenSubshiftInvariantSupport."
                        + "support_mem_of_map_eq"),
                H("An invariant shift carries support points to support points"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, Mu, Sp, InMacro, Sp, Operatorname,
                    Grp(F.Id("Measure")), Open, F.Id("X"), Underscore, F.Id("g"), Close,
                    Comma, Sp, Operatorname, Grp(F.Id("map")), Open, SigmaLower, Close,
                    Open, Mu, Close, Sp, Eq, Sp, Mu, Sp, Rightarrow, Sp, Forall, Sp,
                    F.Id("x"), Sp, InMacro, Sp, F.Id("X"), Underscore, F.Id("g"), Comma,
                    Sp, F.Id("x"), Sp, InMacro, Sp, Operatorname, Grp(F.Id("supp")),
                    Open, Mu, Close, Sp, Rightarrow, Sp, SigmaLower, Open, F.Id("x"),
                    Close, Sp, InMacro, Sp, Operatorname, Grp(F.Id("supp")), Open, Mu,
                    Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Take a neighbourhood U of sigma(x) and choose a smaller open "
                    + "neighbourhood V inside it. Continuity makes the inverse image of V "
                    + "a neighbourhood of x, so membership of x in the support gives that "
                    + "inverse image positive mass. The pushforward identity transfers the "
                    + "same mass to V, and monotonicity transfers positivity from V to U."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Iterating the one-step statement shows that every natural translate of "
                + "the support is contained in the support. The support is closed. Since "
                + "the golden subshift action is minimal, a closed subset with this forward "
                + "invariance is either empty or all of X_g. A probability measure is "
                + "nonzero, so its support cannot be empty.")),
            Describe.Lean(
                DescribeId.Create("invariant-probability-full-support"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/GoldenSubshiftInvariantSupport."
                        + "invariant_support_eq_univ"),
                H("Invariant probability measures have full support"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, Mu, Sp, InMacro, Sp, Operatorname, Grp(F.Id("Prob")),
                    Open, F.Id("X"), Underscore, F.Id("g"), Close, Comma, Sp,
                    Operatorname, Grp(F.Id("map")), Open, SigmaLower, Close, Open, Mu,
                    Close, Sp, Eq, Sp, Mu, Sp, Rightarrow, Sp, Operatorname,
                    Grp(F.Id("supp")), Open, Mu, Close, Sp, Eq, Sp, F.Id("X"),
                    Underscore, F.Id("g")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The preceding support propagation gives the invariant-subset input to "
                    + "minimality, while the standard closedness of support gives the "
                    + "topological input. Minimality leaves the empty and universal cases; "
                    + "the nonzero total mass of a probability measure excludes the empty "
                    + "case."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("invariant-probability-open-positive"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/GoldenSubshiftInvariantSupport."
                        + "invariantMeasure_isOpenPosMeasure"),
                H("Invariant probability measures charge every nonempty open set"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, Mu, Sp, InMacro, Sp, Operatorname, Grp(F.Id("Prob")),
                    Open, F.Id("X"), Underscore, F.Id("g"), Close, Comma, Sp,
                    Operatorname, Grp(F.Id("map")), Open, SigmaLower, Close, Open, Mu,
                    Close, Sp, Eq, Sp, Mu, Sp, Rightarrow, Sp, Operatorname,
                    Grp(F.Id("IsOpenPosMeasure")), Open, Mu, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Apply the full-support conclusion to the invariant probability measure, "
                    + "then use the converse to Mathlib's support theorem established at the "
                    + "start. Thus every nonempty open subset of X_g has positive measure."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-invariant-open-positive-measure"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/GoldenSubshiftInvariantSupport."
                        + "golden_invariant_isOpenPosMeasure"),
                H("The golden subshift carries an open-positive invariant measure"),
                StatementSource.FromAuthor(Disp(Seq(
                    Exists, Sp, Mu, Sp, InMacro, Sp, Operatorname, Grp(F.Id("Prob")),
                    Open, F.Id("X"), Underscore, F.Id("g"), Close, Comma, Sp, Open,
                    Operatorname, Grp(F.Id("Measurable")), Open, SigmaLower, Close, Sp,
                    Land, Sp, Operatorname, Grp(F.Id("map")), Open, SigmaLower, Close,
                    Open, Mu, Close, Sp, Eq, Sp, Mu, Close, Sp, Land, Sp, Operatorname,
                    Grp(F.Id("IsOpenPosMeasure")), Open, Mu, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Take the invariant probability measure constructed upstream. Its "
                    + "measure-preserving certificate supplies both displayed fields: sigma "
                    + "is measurable and its pushforward fixes the measure. The general "
                    + "result above supplies positivity on every nonempty open set."))),
                DescribeRole.Theorem))));
}
