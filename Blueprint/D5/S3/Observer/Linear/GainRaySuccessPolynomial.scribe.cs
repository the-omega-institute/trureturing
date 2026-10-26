using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class GainRaySuccessPolynomialDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual chart polynomial success certificates", H("Actual chart polynomial success certificates"), Blocks(
            Paragraph(Text("ChartPolynomial d is the real multivariate polynomial ring with d+4 variables. The coordinate order is x,r,beta(0),...,beta(d),delta. The source denominator is D=1+x*r, positive on the chart. For a real matrix A the trace numerator is A00+A01*x+A10*r+A11*x*r. The polynomial for read i is that numerator times the ordinary gain sum over k of beta(k)*i^k, plus delta*D. The output polynomial is the fixed C-weighted sum of these read polynomials. chartWedge uses beta(j) times output(k) minus beta(k) times output(j). These definitions use the same source, whole gain and drift at every clock.")),
            Describe.Lean(DescribeId.Create("gain-ray-gainraysuccesspolynomial-eval-chart-wedge"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRaySuccessPolynomial.eval_chart_wedge"),
                H("The cleared wedge is the native output wedge"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every d,w,C, positive real x,r, nonzero beta:Coeff d, arbitrary drift delta, and j,k in Fin(d+1), evaluation of chartWedge(d,w,C,j,k) at chartParameters(d,x,r,beta,delta) equals (1+x*r) times [beta(j) times (C readings(chartWorld(d,x,r,beta,delta),w))(k) minus beta(k) times that output at j]. Each read uses acquisition(take i w) and the literal clock i, including i=0."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gain-ray-gainraysuccesspolynomial-chart-wedge-nonzero-iff"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRaySuccessPolynomial.chart_wedge_nonzero_iff"),
                H("Nonzero polynomial witnesses exactly nonuniversal collinearity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural d, word w and fixed C, some chartWedge(d,w,C,j,k) is a nonzero polynomial if and only if it is false that C readings(W,w) is collinear with W.coeff at every original World d W. This is an equivalence on the entire source and gain domain. The reverse source chart is exact. A nonzero coefficient vector is collinear with an output precisely when all its coordinate wedges vanish. To obtain a polynomial identity from universal collinearity, evaluate on the product domain x>0,r>0 with all coefficient and drift coordinates arbitrary; at the zero coefficient vector each wedge also vanishes algebraically."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gain-ray-gainraysuccesspolynomial-success-chart-wedge-zero"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRaySuccessPolynomial.success_chart_wedge_zero"),
                H("Each actual successful output satisfies every wedge equation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every d,w,C, positive x,r, nonzero whole coefficient vector beta, arbitrary delta and j,k in Fin(d+1), if C succeeds at chartWorld(d,x,r,beta,delta), evaluation of chartWedge(d,w,C,j,k) at those coordinates is zero. The success scale can be any nonzero real, of either sign. Sampled roots, lower actual degree, repeated roots and arbitrary drift are included."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gain-ray-gainraysuccesspolynomial-chart-success-certificate"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRaySuccessPolynomial.chart_success_certificate"),
                H("A nonuniversal readout has an explicit nonzero success polynomial"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every d,w,C failing whole-domain universal collinearity, there exist j,k in Fin(d+1) such that chartWedge(d,w,C,j,k) is nonzero, its evaluation vanishes at every positive-chart world where C succeeds, and its evaluation is nonzero for Lebesgue-almost every ambient coordinate vector in Fin(d+4) to the reals. Almost-everywhere nonvanishing is the direct application of GenericLieLength.ae_mvPolynomial_ne_zero to this polynomial. This ambient statement alone asserts no result about substitution into a prescribed-history fiber."))), DescribeRole.Theorem))));
}
