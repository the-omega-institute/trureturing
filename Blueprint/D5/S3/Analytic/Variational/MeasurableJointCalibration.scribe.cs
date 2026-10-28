using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Variational;

internal sealed class MeasurableJointCalibrationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integrable square remainders and absolute-continuity transport give quantitative comparison and rigidity for measurable reciprocal densities.",
        H("Measurable Joint Calibration"),
        Blocks(
            Entry("Calibration", "reference-data", "Smooth reference equations",
                "For a real parameter b and real functions Z,Q,M,N, Calibration requires Z and M to be infinitely differentiable at every point of [0,1], Q continuous on that interval, Z'=Q, M'=N, Z>0, Q>0, M(r)=8bQ(r)/9+8rQ(r)^2/(9Z(r)), and N(r)=-8rQ(r)^3/(27Z(r)^2). These conditions apply to the reference, independently of the competitor. The remainder theorem uses these differential and algebraic equations rather than assuming a comparison or an equality characterization.",
                DescribeRole.Definition),
            Entry("defect", "defect", "The reciprocal square defect",
                "For real functions u,U,Q, defect(u,U,Q,x)=u(x)[sqrt(x)/u(x)-(2/3)Q(U(x))]^2. The factor 2/3 converts the derivative of x sqrt(x) to the original reciprocal square-root coordinate.",
                DescribeRole.Definition),
            Entry("potential", "potential", "The calibrated potential",
                "For real functions U,Z,M, potential(U,Z,M,x)=M(U(x))[x sqrt(x)-Z(U(x))/2]. Its endpoint difference is the comparison constant.",
                DescribeRole.Definition),
            Entry("bounded_positive_integrability", "integrability", "Individual bounds imply reciprocal integrability",
                "Let u be a.e. measurable for volume restricted to [1,2]. Suppose there are real c,B with c>0 and c<=u(x)<=B a.e. Then u, x/u(x), and [integral from 1 to x of u]/u(x)^2 are interval integrable on [1,2]. The cumulative integral is continuous and bounded on this compact interval. The positive lower bound controls both reciprocal terms. The constants may depend on u; no common bounds or regularity of u are required.",
                DescribeRole.Theorem),
            Entry("remainder", "remainder", "Global remainder and zero-energy transport",
                "Let b be any real number and let Z,Q,M,N satisfy Calibration. Let u be a.e. measurable on [1,2] with its own positive lower and finite upper bounds. Let U be absolutely continuous on [1,2], map this interval into [0,1], have derivative u a.e., and satisfy U(1)=0. Suppose Z(0)=1 and the density L(x)=b x/u(x)+U(x)/u(x)^2 is interval integrable. Then the defect is interval integrable, its integral E is nonnegative, and potential(2)-potential(1)+bE<=integral L. If E=0, then sqrt(x)/u(x)=(2/3)Q(U(x)) a.e. and Z(U(x))=x sqrt(x) at every x in the entire closed interval [1,2]. There is no smoothness or inverse assumption on u or U. Nonnegative b is unnecessary for this calibrated estimate; positivity is used when an application infers E=0 from equality of cost.",
                DescribeRole.Theorem,
                "The scalar cubic tangent gap is nonnegative by a two-case polynomial identity. Retaining the exact quadratic gap 4b(q-Q)^2/9 and substituting q=3 sqrt(x)/(2u(x)) gives precisely b times the original square defect after multiplication by u. Before comparing integrals, compact continuity of Q composed with U and the individual density bounds prove integrability. Smoothness makes Z and M Lipschitz on the compact range, so their compositions with U and the potential are absolutely continuous. The a.e. chain rule and the fundamental theorem of calculus integrate the calibrated inequality. Zero nonnegative integrable energy gives the reciprocal slope equation a.e.; the absolutely continuous function Z(U(x))-x sqrt(x) then has derivative zero a.e. and is constant. Its value at 1 is zero, including the endpoints in the resulting identity."),
            Entry("primitive_congr", "primitive-congruence", "Cumulative integrals respect null sets",
                "If real functions u and v agree a.e. for volume restricted to [1,2], their integrals from 1 to x agree for every x in [1,2]. Restrict the same a.e. identity to each initial interval. This preserves all null-set representatives when the calibration is applied to an optimizer.",
                DescribeRole.Theorem))));

    private static DocumentBlock Entry(string name, string id, string title, string text,
        DescribeRole role, string proof = "") => Describe.Lean(
            DescribeId.Create("measurable-joint-calibration-" + id),
            DeclarationHandle.Create("D5/S3/Analytic/Variational/MeasurableJointCalibration." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            proof.Length == 0 ? Blocks(Paragraph(Text(text))) :
                Blocks(Paragraph(Text(text)), Paragraph(Text(proof))), role);
}
