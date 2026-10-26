using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class PolynomialL2DerivativeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/PolynomialL2Derivative.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shifted Legendre orthogonality bounds complex polynomial derivative energy by a fourth power of the dimension.",
        H("Complex Polynomial L2 Derivative Energy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complex-polynomial-derivative-l2-of-degree"),
                DeclarationHandle.Create(Prefix + "complex_polynomial_derivative_l2_of_degree"),
                H("The degree formulation includes the zero-dimensional space"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural d and every polynomial p with arbitrary complex "
                        + "coefficients and degree(p)<d in WithBot(Nat), the integral from zero to one "
                        + "of norm(p'(x)) squared is at most d^4 times the integral of norm(p(x)) "
                        + "squared. Evaluation uses the real input embedded in the complex numbers, "
                        + "and both integrals use real Lebesgue measure. There is no nonzero "
                        + "polynomial hypothesis. At d=0 the degree premise forces p=0, and the "
                        + "same statement gives the zero-energy boundary case.")),
                    Paragraph(Text("The proof maps Mathlib's integer shifted Legendre polynomials "
                        + "to complex polynomials L_n. In this convention L_n(0)=1 and "
                        + "L_n(1)=(-1)^n. Rodrigues' identity is n! L_n=D^n[X^n(1-X)^n]. "
                        + "Every derivative of the Rodrigues primitive of order below n vanishes "
                        + "at both endpoints, by divisibility by the remaining positive powers "
                        + "of X and 1-X. Repeated integration by parts transfers n derivatives "
                        + "onto a test polynomial. Its derivative vanishes when its degree is "
                        + "below n, which proves lower-degree orthogonality.")),
                    Paragraph(Text("The beta integral of x^n(1-x)^n is n!^2/(2n+1)!. "
                        + "Together with the leading coefficient this gives the exact squared "
                        + "L2 norm integral norm(L_n(x))^2 dx=1/(2n+1). Conjugation is retained "
                        + "explicitly: mapping the coefficients by complex conjugation conjugates "
                        + "the value at real x, while L_n itself has real coefficients. Thus "
                        + "orthogonality is Hermitian orthogonality for arbitrary complex "
                        + "coefficients, rather than only a real-coefficient calculation.")),
                    Paragraph(Text("One more integration by parts expresses the derivative energy "
                        + "through endpoint values; the integral involving L_n'' vanishes by "
                        + "the proved lower-degree orthogonality. The endpoint derivatives are "
                        + "L_n'(0)=-n(n+1) and L_n'(1)=(-1)^n n(n+1). Consequently the exact "
                        + "derivative energy is integral norm(L_n')^2=2n(n+1), also for n=0.")),
                    Paragraph(Text("The polynomial-sequence spanning theorem supplies an expansion "
                        + "p=sum_(n<d) a_n L_n for every polynomial of degree below d, including "
                        + "the empty expansion at d=0. Explicit conjugation gives Parseval: "
                        + "E(p)=integral norm(p)^2=sum_(n<d) norm(a_n)^2/(2n+1). Weighted "
                        + "finite Cauchy-Schwarz bounds norm(p'(x))^2 by E(p) times "
                        + "sum_(n<d) (2n+1) norm(L_n'(x))^2. Integrating that finite density "
                        + "gives sum_(n<d) (2n+1)2n(n+1)=d^2(d^2-1), at most d^4. "
                        + "Continuity supplies each integrability premise. No exponential "
                        + "coefficient estimate or assumed analytic budget enters this proof.")),
                    Paragraph(Text("This source combines classical Rodrigues orthogonality, beta "
                        + "normalization, polynomial spanning and Cauchy-Schwarz, reusing the "
                        + "pinned Mathlib shifted-Legendre, integration-by-parts and beta APIs. "
                        + "No literature originality claim is made. The supporting Legendre "
                        + "identities and sharper intermediate budget are private proof steps; "
                        + "the public assertion here is the displayed d^4 inequality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("complex-polynomial-derivative-l2"),
                DeclarationHandle.Create(Prefix + "complex_polynomial_derivative_l2"),
                H("The dimension-bounded form and the pending reciprocal-tail use"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural d with 1<=d and every complex polynomial p "
                        + "with natDegree(p)<d, the same derivative energy is at most d^4 E(p). "
                        + "All four source binders d, the proof of 1<=d, p and the degree proof "
                        + "are retained. The zero polynomial is allowed, as are arbitrary "
                        + "complex coefficients. The proof applies the degree theorem using "
                        + "degree(p)<=natDegree(p); it introduces no further analytic assumption.")),
                    Paragraph(Text("For the pending actual reciprocal-tail application, the energy "
                        + "estimate supplies a polynomial variation allowance. Writing g(x)=norm(p(x))^2, "
                        + "the classical product rule and integral Cauchy-Schwarz give "
                        + "integral abs(g')<=2 sqrt(E(p') E(p))<=2d^2 E(p). In particular, "
                        + "an energy-normalized polynomial contributes at most 2d^2 to this "
                        + "variation allowance. For two polynomials p and q the same reasoning "
                        + "bounds the variation of p times conjugate(q) by "
                        + "(d_p^2+d_q^2) sqrt(E(p) E(q)), under their respective degree bounds. "
                        + "These are application derivations in the narrative; this module "
                        + "does not export separate Lean variation theorems.")),
                    Paragraph(Text("If the actual reciprocal factor r in that consumer is "
                        + "continuously differentiable on the integration interval and has "
                        + "bounds norm(r)<=M and norm(r')<=N there, the product rule gives "
                        + "integral norm((r g)')<=(2M d^2+N) E(p). For r=1/F these bounds "
                        + "require an actual positive lower bound on norm(F) and control of "
                        + "F'; reciprocal differentiation alone does not supply them. A signed "
                        + "tail argument must also supply its actual primitive or cumulative "
                        + "tail bound and the integration-by-parts boundary terms. This "
                        + "polynomial estimate pays the polynomial part of that calculation; "
                        + "it does not construct the actual reciprocal, its tail, or an enclosure.")),
                    Paragraph(Text("The substantive actual reciprocal consumer remains uncompiled "
                        + "and pending. Its exact definitions, nonvanishing hypotheses, tail "
                        + "bounds, endpoint costs and final enclosure still require native "
                        + "verification in the consuming development. This Reg/Scribe component "
                        + "is intended for integration with that actual consumer. No formal "
                        + "Riemann-hypothesis or Robin implication is established here."))),
                DescribeRole.Theorem))));
}
