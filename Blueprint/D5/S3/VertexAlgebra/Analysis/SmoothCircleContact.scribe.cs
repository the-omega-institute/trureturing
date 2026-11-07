using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Analysis;

internal sealed class SmoothCircleContactDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Smooth-circle Fourier products and finite contact expansion",
        H("Smooth-circle Fourier products and finite contact expansion"),
        Blocks(
            Paragraph(Text("Mathlib supplies completion, normed operators, Fourier analysis, integer binomial identities and unconditional sum machinery under Apache 2.0. The additional arguments here concern the stated original objects and relations. No literature novelty or physical realization is asserted.")),
            Describe.Lean(DescribeId.Create("smoothcirclecontact-coefficient-frequencybinomial"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.coefficient_frequencyBinomial"),
                H("Fourier multipliers of differential binomials"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A Test is the existing globally smooth complex function of period 2*pi. Define D=-i*d/dtheta and P_0 f=f, P_(j+1) f=(D-j)P_j f/(j+1). For every natural j and integer m, the mth coefficient of P_j f equals choose(m,j)*fhat(m). Periodicity and the fundamental theorem of calculus handle the zero frequency before any division by m."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("smoothcirclecontact-frequencybinomial-product-zero"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.frequencyBinomial_product_zero"),
                H("Differential contact vanishes for a zero product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("If f(theta)*g(theta)=0 for every real theta, then (P_j f)(theta)*g(theta)=0 for every natural j and real theta. At a point where g is nonzero, continuity supplies a neighborhood where f vanishes, and every derivative of f vanishes there."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("smoothcirclecontact-product-zero-of-disjoint-tsupport"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.product_zero_of_disjoint_tsupport"),
                H("Closed quotient-circle support separation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Disjoint closed supports of the actual periodic lifts on AddCircle(2*pi) imply f(theta)*g(theta)=0 for all real theta. The supports are defined on the quotient circle, including the seam."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("smoothcirclecontact-fouriercoeff-mul-hassum"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.fourierCoeff_mul_hasSum"),
                H("Fourier coefficient of a pointwise product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For continuous complex F,G on AddCircle(T), T>0, absolute summability of the Fourier coefficients of F implies that sum over all integer m of Fhat(m)*Ghat(t-m) has sum the tth coefficient of the pointwise product F*G, and the scalar series is absolutely summable. Uniform Fourier reconstruction is followed by the bounded linear coefficient functional of multiplication by G."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("smoothcirclecontact-double-smear-absolute"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.double_smear_absolute"),
                H("Absolute double smearing"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Let E be any complete complex normed space and C:Z->Z->E satisfy norm C(m,n)<=K*(1+abs(m))^R*(1+abs(n))^R with K>=0 and natural R. Every pair of genuine Tests f,g gives an absolutely norm-summable series fhat(m)*ghat(n) acting on C(m,n) over Z x Z, bounded termwise by the product of the two existing weighted Fourier majorants."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("smoothcirclecontact-contact-series-absolute"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.contact_series_absolute"),
                H("Absolute contact rows"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For the same original C, bound K,R and every natural j, the series over t in Z of the norm of the coefficient of (P_j f)*g at t acting on c_j(t) is summable. This follows from the absolute double majorant after the bijection (t,m)->(m,t-m), before evaluating any iterated sum."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("smoothcirclecontact-delta-smooth-contact-formula"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.delta_smooth_contact_formula"),
                H("Finite Banach-valued contact formula"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every complete complex normed E, natural R,N, K>=0 and C with the stated polynomial bound and delta^N C=0, the double smear equals sum over j<N and all integer t of coefficient(((P_j f)*g),t) acting on c_j(t). The conclusion includes absolute convergence of the original double series and every contact series. Newton reconstruction is followed only by rearrangements justified by absolute summability. At N=0 the contact sum is empty."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("smoothcirclecontact-double-smear-eq-zero-of-product-zero"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.double_smear_eq_zero_of_product_zero"),
                H("Vanishing of a double smear"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Under the same hypotheses on E,C,K,R,N, if the genuine tests have pointwise zero product, the full double smear is zero. Each differential contact product vanishes, so every term of the finite contact expansion is zero."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("smoothcirclecontact-double-smear-eq-zero-of-disjoint-tsupport"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Analysis/SmoothCircleContact.double_smear_eq_zero_of_disjoint_tsupport"),
                H("Separated smooth supports annihilate finite contact"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Under those same Banach-space growth and delta hypotheses, disjoint closed supports of the actual quotient-circle lifts imply the full all-integer double smear is zero. This statement concerns the original coefficients and genuine smooth tests; no commutation conclusion is an input."))), DescribeRole.Theorem)),
        []));
}
