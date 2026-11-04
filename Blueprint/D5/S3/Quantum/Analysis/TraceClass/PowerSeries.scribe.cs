using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.TraceClass;

internal sealed class PowerSeriesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/TraceClass/PowerSeries.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Noncommuting trace power errors and absolutely convergent trace logarithms.",
        H("Trace-class positive-power series"),
        Blocks(
            Paragraph(Text("H is any complete complex inner product space, including the zero space. T and S are elements of the existing genuine trace-class carrier. The analytic trace, its ideal estimates and bounded trace pairing are the attributed Physlib suppliers, with Tom Ole Diem's authorship preserved in those sources. No new trace or determinant infrastructure is introduced.")),
            N("power_error_le", "Noncommuting telescoping estimate", "For any real q>=0 bounding both operator norms and every m>=0, the trace-class norm of T^(m+1)-S^(m+1) is at most (m+1)*q^m*norm(T-S). Inductive telescoping uses T^(m+1)*(T-S)+(T^(m+1)-S^(m+1))*S at the successor step. Each factor multiplication uses the genuine two-sided trace ideal norm estimate. No exchange of T and S or trace cyclicity is required, and no zeroth power is assumed trace class."),
            N("powerTrace_error_le", "Power traces", "Applying the actual bounded linear trace functional to the preceding trace-class difference proves the same bound for the absolute difference of the genuine traces of the positive powers. The zeroth exponent q^0=1 is retained, so q=0 is in scope."),
            N("logTerm_norm_summable", "Absolute logarithmic convergence", "If 0<=q<1 bounds the operator norm of T, the series of norms of logTerm(T,m)=Tr(T^(m+1))/(2*(m+1)) is summable. The genuine trace bound gives norm(Tr(T^(m+1)))<=norm(T)_1*q^m. Dividing by the positive m+1 and dominating by norm(T)_1*q^m/2 reduces absolute convergence to the real geometric series."),
            N("traceLog_error_le", "Quantitative trace logarithm continuity", "For two trace-class operators with operator norms bounded by the same 0<=q<1, the norm of the difference of their traceLog sums is at most norm(T-S)_1/(2*(1-q)). The noncommuting power estimate cancels the positive natural m+1 termwise, leaving norm(T-S)_1*q^m/2. Absolute summability justifies subtraction of the genuine series and the geometric sum yields the bound. No division by q occurs. The native Gaussian cutoff module consumes this estimate on the separately compressed products."),
            Paragraph(Text("These are analytic consequences of the explicit noncommuting telescoping construction and existing trace ideals, without a mathematical novelty claim. They do not supply a finite Gaussian identity, a determinant interpretation or any physical equivalence. Faithful four-slot dependent-family registration is unfinished under issues 24524 and 24498; no declared_validated status is claimed."))),
        []));

    private static DocumentBlock N(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("trace-class-power-series-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
