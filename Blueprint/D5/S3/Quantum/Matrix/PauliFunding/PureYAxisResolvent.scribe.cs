using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.PauliFunding;

internal sealed class PureYAxisResolventDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact parity resolvents and all-order moments of two-dimensional Pauli control blocks.",
        H("Parity resolvents of real control blocks"), Blocks(
            Entry("controlBlock", "Actual control block",
                "For arbitrary real a and t, H(a,t) is the real matrix "
                + "[[(1+a)/4,t/4],[t/4,(1-a)/4]]. For a pure Y-axis source, "
                + "t=mu sqrt(1-a squared) and the two blocks are H(a,t) and H(a,-t).",
                DescribeRole.Definition),
            Entry("controlFilter", "Shifted control filter",
                "For arbitrary real a,t,s, P(a,t,s)=H(a,t)(H(a,t)+sI) inverse. "
                + "The inverse is Mathlib's nonsingular inverse; subsequent statements use s>0.",
                DescribeRole.Definition),
            Entry("h", "Control determinant numerator",
                "For real a,t, h(a,t)=1-a squared-t squared. "
                + "This is sixteen times the determinant of H(a,t).", DescribeRole.Definition),
            Entry("denom", "Shifted determinant numerator",
                "For real a,t,s, R(a,t,s)=8s(1+2s)+h(a,t). "
                + "It is sixteen times the determinant of H(a,t)+sI.", DescribeRole.Definition),
            Entry("alpha", "Half parity trace",
                "Define alpha(a,t,s)=4sa/R(a,t,s) for all real parameters.", DescribeRole.Definition),
            Entry("beta", "Negative parity determinant",
                "Define beta(a,t,s)=h(a,t)/R(a,t,s) for all real parameters.", DescribeRole.Definition),
            Entry("moment", "Actual cyclic product moment",
                "For real a,t,s and natural j, moment(a,t,j,s) is "
                + "the trace of (P(a,-t,s)P(a,t,s)) to the j-th power.", DescribeRole.Definition),
            Entry("resolvent_spectral_data", "Exact shifted resolvent and parity data",
                "For every real a,t,s with 0<=a<=1, t squared<=1-a squared and s>0, "
                + "R is strictly positive, alpha and beta are nonnegative, and the exact filter is "
                + "[[(4s+h+4sa)/R,4st/R],[4st/R,(4s+h-4sa)/R]]. "
                + "With Z=diag(1,-1), the negative filter equals ZP(a,t,s)Z, "
                + "the trace of ZP(a,t,s) is 2alpha, and its determinant is -beta. "
                + "These identities include h=0; invertibility is required only after the positive shift."),
            Entry("moment_eq_evenMoment", "All-order exact matrix moment",
                "For every real a,t,s with 0<=a<=1, t squared<=1-a squared and s>0, "
                + "and every natural j, moment(a,t,j,s) equals "
                + "(alpha+sqrt(alpha squared+beta)) to the power 2j plus "
                + "(alpha-sqrt(alpha squared+beta)) to the power 2j. "
                + "Parity makes P(a,-t,s)P(a,t,s) the square of ZP(a,t,s); "
                + "the Vieta power-trace identity supplies all orders, including repeated roots."),
            Entry("moment_comparison", "Every-order matrix comparison",
                "For every real a,t,s with 0<=a<=1, t squared<=1-a squared and s>0, "
                + "and every natural j, a to the power 2j divided by (1+2s) to the power 2j "
                + "is at most moment(a,t,j,s). The characteristic polynomial evaluated at a/(1+2s) "
                + "equals beta times ((a/(1+2s)) squared-1), which is nonpositive."),
            Entry("moment_strict", "Strict comparison in the positive determinant case",
                "For every real a,t,s with 0<=a<=1, t squared<=1-a squared, h(a,t)>0 and s>0, "
                + "and every natural j>=1, a to the power 2j divided by (1+2s) to the power 2j "
                + "is strictly less than moment(a,t,j,s). The comparison polynomial is strictly negative."),
            Entry("moment_boundary", "Exact rank-one boundary",
                "For every real a,t,s with 0<=a<=1, t squared<=1-a squared, h(a,t)=0 and s>0, "
                + "and every natural j>=1, moment(a,t,j,s) equals a to the power 2j "
                + "divided by (1+2s) to the power 2j. This includes a=0 and the zero product moment."),
            Entry("complexFilter", "Actual complex shifted filter",
                "For real a,t,s, complexFilter(a,t,s) is Hc(Hc+sI) inverse, "
                + "where Hc is the entrywise complex embedding of H(a,t). "
                + "Thus it uses the actual complex matrix inverse rather than an assumed embedding rule.",
                DescribeRole.Definition),
            Entry("complexMoment", "Actual complex sandwich moment",
                "For real a,t,s and natural j, complexMoment(a,t,j,s) is the real part of "
                + "the trace of (sqrt(Pc(a,-t,s))Pc(a,t,s)sqrt(Pc(a,-t,s))) to the j-th power. "
                + "The square root is the positive square root from the continuous functional calculus.",
                DescribeRole.Definition),
            Entry("complex_moment_eq_real", "Complex square-root sandwich and real cyclic product",
                "For every real a,t,s with 0<=a<=1, t squared<=1-a squared and s>0, "
                + "and every natural j, complexMoment(a,t,j,s)=moment(a,t,j,s). "
                + "The embedded shifted filter equals the embedding of the real filter. "
                + "The exact filter formula proves positive semidefiniteness, including h=0; "
                + "the square of its positive square root is therefore the filter itself. "
                + "Cyclicity of power traces proves the equality without requiring either unshifted block "
                + "or either filter to be invertible. In fact the full complex sandwich trace "
                + "is the real embedding of the real product moment."))));

    private static DocumentBlock Entry(string name, string title, string prose,
        DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-')), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
