using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves;
internal sealed class A6QuarticEstimatesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6QuarticEstimates." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("The current compiler statement below supplies the exact telescope, hypotheses and conclusion. The full domain and original boundaries in this document apply."))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive-domain quartic analytic and height estimates", H("Positive-domain quartic analytic and height estimates"),
        Blocks(
            Paragraph(Text("For every positive real b, the original Fstar is strictly decreasing with its exact limit and u0=0. The improper integral is positive and strictly less than1/(sqrt43645 b). On both signs of every integer quartic point, |W|<3649b^2 and the actual rational Weil logarithmic height of R_U is bounded by log13540800+2log b. These input estimates do not provide a complete Tzanakis bound, regulator or David constants, rank/saturation, certified LLL or exhaustive point list. The Equation26 printed-factor discrepancy remains unresolved.")),
            Paragraph(Text("Source: original Nikandish problem; Ma/Nikandish/Zhang supplied manuscripts at PR9 revision6d491f77b35dec808fc777b69939c56cdae5dc02. Exact source blob and attribution are retained in Lean. All O1-O9, L1-L21/F1-F17, C1-C16 outcomes and original rights/publication boundaries remain binding. Exact n7 and its pause, generalQ3, a6 certification and finite-enumeration reproduction limits are unchanged.")),
            Item("quartic-gt-leading", "quartic_gt_leading", "quartic gt leading"),
            Item("quartic-positive", "quartic_positive", "quartic positive"),
            Item("hasderivat-f", "hasDerivAt_f", "hasDerivAt f"),
            Item("hasderivat-fstar", "hasDerivAt_Fstar", "hasDerivAt Fstar"),
            Item("derivative-identity", "derivative_identity", "derivative identity"),
            Item("derivative-negative", "derivative_negative", "derivative negative"),
            Item("fstar-strictanti", "Fstar_strictAnti", "Fstar strictAnti"),
            Item("quartic-upper", "quartic_upper", "quartic upper"),
            Item("both-signs-w-bound", "both_signs_W_bound", "both signs W bound"),
            Item("chart-numerator-bound", "chart_numerator_bound", "chart numerator bound"),
            Item("height-int-div", "height_int_div", "height int div"),
            Item("rational-chart-height", "rational_chart_height", "rational chart height"),
            Item("inverse-sqrt-lt", "inverse_sqrt_lt", "inverse sqrt lt"),
            Item("tail-integrable", "tail_integrable", "tail integrable"),
            Item("tail-integral-bound", "tail_integral_bound", "tail integral bound"),
            Item("tail-integral-positive", "tail_integral_positive", "tail integral positive"),
            Item("fstar-gt-asymptote", "Fstar_gt_asymptote", "Fstar gt asymptote"),
            Item("fstar-limit", "Fstar_limit", "Fstar limit"),
            Item("fstar-excluded-values", "Fstar_excluded_values", "Fstar excluded values")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6EllipticModels"))]));
}
