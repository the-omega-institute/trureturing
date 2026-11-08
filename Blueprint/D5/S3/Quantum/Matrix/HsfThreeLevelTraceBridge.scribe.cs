using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class HsfThreeLevelTraceBridgeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complex PSD3 cubic geometry and exact scalar coefficients.",
        H("HsfThreeLevelTraceBridge"),
        Blocks(
            Entry("tauClosed", "tauClosed",
                "The literal first closed moment 3sqrt(pq)(p+q)/(2H).", DescribeRole.Definition),
            Entry("kappaClosed", "kappaClosed",
                "The literal antisymmetric closed current moment sqrt(pq)(q-p)(p^2+3pq+q^2)/(2H^2).", DescribeRole.Definition),
            Entry("psiClosed", "psiClosed",
                "The literal closed moment p^2q^2sqrt(pq)(p+q)/H^3.", DescribeRole.Definition),
            Entry("betaNumerator", "betaNumerator",
                "The explicit rational-kernel numerator G, before division by the positive H factors.", DescribeRole.Definition),
            Entry("betaClosed", "betaClosed",
                "The literal closed moment sqrt(pq)r^3G/(2H(p,q)H(q,r)^2H(r,p)^2).", DescribeRole.Definition),
            Entry("orderedCoefficient", "orderedCoefficient",
                "The scalar coefficient 4tau beta-4tau tau psi-(2/27)tau tau tau+3tau kappa kappa. The last plus sign comes from K*=-K.", DescribeRole.Definition),
            Entry("rawNumerator", "rawNumerator",
                "The explicit polynomial 8Q^3 times the actual ordered scalar coefficient, cleared before symmetrization.", DescribeRole.Definition),
            Entry("momentMatrix", "momentMatrix",
                "Entrywise multiplication of the actual source by the indicated real two-level moment kernel.", DescribeRole.Definition),
            Entry("jMatrix", "jMatrix",
                "The second source-dependent moment with entry sum over k of beta(p_i,p_j;p_k)S_ik S_kj.", DescribeRole.Definition),
            Entry("closedMomentTrace", "closedMomentTrace",
                "The four closed ordered traces 4Tr(XJv)-4Tr(XXPsi)-(2/27)Tr(XXX)-3Tr(XK* K), using the literal closed moment functions.", DescribeRole.Definition),
            Entry("orderedCubic", "orderedCubic",
                "The full sum over all 27 ordered triples, with the real part of the original three source factors.", DescribeRole.Definition),
            Entry("trace_to_ordered", "trace to ordered",
                "The four finite trace expressions expand into the actual 27 ordered scalar terms. Matrix factors are kept in their original order until scalar coordinates are expanded.", DescribeRole.Theorem),
            Entry("ordered_to_coordinates", "ordered to coordinates",
                "If the pure, repeated-index, forward-cycle and reverse-cycle scalar coefficient sums match their displayed values, the 27-term ordered Hermitian cubic equals the three pair terms plus k Re(S01 S12 S20). This is coefficient algebra, not an assumed inequality.", DescribeRole.Theorem),
            Entry("closed_trace_normal_form", "closed trace normal form",
                "At all positive levels, the four finite closed-moment traces equal the actual rho/Xi coordinate cubic, with both cycle orientations and all repeated-index terms.", DescribeRole.Theorem),
            Entry("closed_trace_nonneg", "closed trace nonneg",
                "The four finite closed-moment traces are nonnegative for every complex PSD three by three source and all positive levels. Equality with the original integrals and the original HSF derivative is a separate unfinished bridge.", DescribeRole.Theorem),
            Paragraph(Text("The statements concern the explicitly defined closed algebraic kernels. "
                + "The commutant equality classification, identification with the original integrals, "
                + "dominated differentiation and original HSF derivative/source bridge remain outside these results. "
                + "No assertion about arbitrary matrix dimension or literature novelty follows.")))));

    private static DocumentBlock Entry(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("hsfthreeleveltracebridge-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
