using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ReciprocalGammaTuran;

internal sealed class SeriesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Convergent reciprocal Gamma series and boundary Turanian recurrences.",
        H("The entire series and its coefficients"), Blocks(
            Entry("reciprocal-gamma-series", "F", "The reciprocal Gamma series",
                "For real b and x, F(b,x) is the sum over natural n of rgamma(n+b) times x to the power n.", DescribeRole.Definition),
            Entry("reciprocal-gamma-formal-series", "formalSeries", "Formal coefficient sequences",
                "For a real sequence g and real b, formalSeries(g,b) has coefficient g(n)rgamma(n+b) in every natural degree n.", DescribeRole.Definition),
            Entry("boundary-turan-series", "boundarySeries", "The boundary Turanian",
                "For every real t, the formal boundary series is formalSeries(1,0) squared minus formalSeries(1,-t) times formalSeries(1,t).", DescribeRole.Definition),
            Entry("boundary-turan-coefficient", "d", "Boundary coefficients",
                "For real t and natural m, d(t,m) is the degree m coefficient of the formal boundary series.", DescribeRole.Definition),
            Entry("reciprocal-gamma-infinite-radius", "entire_series", "Infinite convergence radius",
                "For every real b, F(b,.) has the scalar power series with coefficients rgamma(n+b) around zero on the ball of infinite radius. The norm bounds hold at every nonnegative radius.", DescribeRole.Theorem),
            Entry("reciprocal-gamma-series-convergence", "hasSum_series", "Convergence at every argument",
                "For every real b and x, the defining series sums to F(b,x). The terms are absolutely summable: beyond the finitely many nonpositive Gamma arguments, the ratio is x divided by n+b and tends to zero.", DescribeRole.Theorem),
            Entry("reciprocal-gamma-cauchy-coefficient", "coeff_mul", "Exact formal Cauchy coefficients",
                "For every real sequence g, real mu, alpha and beta, and natural m, the coefficient of formalSeries(g,mu+alpha)formalSeries(g,mu+beta) minus formalSeries(g,mu)formalSeries(g,mu+alpha+beta) equals turanCoeff(g,mu,alpha,beta,m). The finite summation bounds justify replacing the natural difference m-k by its real value.", DescribeRole.Theorem),
            Entry("reciprocal-gamma-boundary-identification", "turanCoeff_one_boundary", "Boundary specialization",
                "For every real t and natural m, turanCoeff(1,-t,t,t,m) equals d(t,m).", DescribeRole.Theorem),
            Entry("reciprocal-gamma-cauchy-convergence", "hasSum_turanCoeff", "Coefficients of the actual products",
                "For real mu, alpha, beta and x, the series with terms turanCoeff(1,mu,alpha,beta,m)x to the power m sums to F(mu+alpha,x)F(mu+beta,x) minus F(mu,x)F(mu+alpha+beta,x). Absolute convergence of each factor permits the Cauchy product and subtraction, identifying the finite formula with the ordinary power series coefficient.", DescribeRole.Theorem),
            Entry("reciprocal-gamma-zero-parameter", "F_zero", "The zero parameter exponential",
                "For every real x, F(0,x) equals x times exp(x). The Gamma values at positive integers give the factorial coefficients, and the value at zero vanishes.", DescribeRole.Theorem),
            Entry("reciprocal-gamma-derivative", "hasDerivAt_F", "Termwise differentiation",
                "For real b and x, F(b,.) has derivative F(b,x)+(1-b)F(b+1,x) at x. The differentiated series has a summable bound on every bounded interval.", DescribeRole.Theorem),
            Entry("reciprocal-gamma-differential-equation", "differential_recurrence", "The differential equation",
                "For all real b and x, x times the derivative of F(b,.) at x equals (x+1-b)F(b,x)+(b-1)rgamma(b). This formula also holds at x=0 and at every parameter pole.", DescribeRole.Theorem),
            Entry("reciprocal-gamma-formal-differential-equation", "formal_recurrence", "The formal differential equation",
                "For real b and f=formalSeries(1,b), X times the formal derivative of f equals (X+1-b)f plus the constant (b-1)rgamma(b). The identity includes poles and follows coefficient by coefficient from the Gamma recurrence.", DescribeRole.Theorem),
            Entry("boundary-forcing-coefficients", "r", "The forcing coefficients",
                "For real t and natural m, r(t,m) equals (t+1)rgamma(-t)rgamma(m+t) plus (1-t)rgamma(t)rgamma(m-t).", DescribeRole.Definition),
            Entry("boundary-formal-differential-equation", "boundary_recurrence", "The boundary differential equation",
                "For real t and the formal boundary series D, X times its derivative is 2(X+1)D plus (t+1)rgamma(-t)formalSeries(1,t) plus (1-t)rgamma(t)formalSeries(1,-t). Applying the Leibniz rule to the two products gives this identity.", DescribeRole.Theorem),
            Entry("boundary-coefficient-recurrence", "coefficient_recurrence", "The boundary coefficient recurrence",
                "For every real t and natural m at least three, (m-2)d(t,m) equals 2d(t,m-1)+r(t,m). This is the degree m coefficient of the formal differential equation.", DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/ReciprocalGammaTuran/Series." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
