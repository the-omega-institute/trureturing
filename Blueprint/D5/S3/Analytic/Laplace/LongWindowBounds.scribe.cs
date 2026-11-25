using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Laplace;

internal sealed class LongWindowBoundsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Zeros/alpoge2026riemann");
    private const string Module = "D5/S3/Analytic/Laplace/LongWindowBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Numerical Landau comparison for arbitrarily late windows",
        H("Numerical bounds behind long-window pole exclusion"),
        Blocks(
            Describe.Remark(DescribeId.Create("landau-growth-source-core"),
                DeclarationHandle.Create(Module + "landau_growth_contra"),
                H("The source numerical growth comparison"),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Alpöge's Deduction.landau_growth_contra proves "
                    + "the existence of eta and U0 by the numerical argument used here. "
                    + "Its proof chooses eta=log(e/d)/2 and U0=2|C|/(c log(e/d)). "
                    + "This original argument is literature-attested.")))),
            Describe.Remark(DescribeId.Create("landau-window-source-core"),
                DeclarationHandle.Create(Module + "landau_window_contra"),
                H("The source numerical window contradiction"),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Alpöge's Deduction.landau_window_contra gives "
                    + "the numerical contradiction for zero less than d less than e at "
                    + "most E. That original statement and argument are literature-attested. "
                    + "The local extension below removes the ordering between e and E.")))),
            Paragraph(Text("The abstract power-window condition consists only of a positive "
                + "width delta and arbitrarily late positive starting points Y whose entire "
                + "interval [Y,Y^(1+delta)] obeys the stated upper bound. Restrictions on "
                + "the exponent are supplied separately by a theorem that needs them.")),
            Describe.Lean(DescribeId.Create("landau-growth-comparison"),
                DeclarationHandle.Create(Module + "landau_growth_contra"),
                H("Uniform comparison of the two geometric rates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Let c,d,e be real numbers with c positive and "
                    + "zero less than d less than e, and let C be any real number. Set "
                    + "eta=log(e/d)/2 and U0=2|C|/(c log(e/d)). Eta is positive and U0 "
                    + "is nonnegative. For every U at "
                    + "least U0 and every natural k at least U, C exp(eta U)/e^k is "
                    + "strictly less than c/d^k. The explicit constants and nonnegative cutoff "
                    + "are the repo-derived strengthening of the cited source statement."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("landau-window-comparison-contradiction"),
                DeclarationHandle.Create(Module + "landau_window_contra"),
                H("The coefficient comparison cannot recur arbitrarily late"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Let c,d,e,E be real numbers with c positive and "
                    + "zero less than d less than e, and d less than E, and let B,K be any real "
                    + "numbers. It is impossible that for every eta positive and every "
                    + "cutoff U0 there exist U at least U0 and a natural k at least U "
                    + "such that c/d^k is at most B/e^k plus K exp(eta U)/E^k. "
                    + "No ordering between e and E is required. This repo-derived extension "
                    + "uses their minimum. Both upper contributions are controlled by "
                    + "the uniform geometric "
                    + "comparison, with their absolute coefficients."))), DescribeRole.Theorem))));
}
