using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sewing;

internal sealed class CanonicalTwoCutScalarDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Absolute convergence of the literal canonical scalar with two internal occupations.",
        H("Canonical two-cut scalar sewing"),
        Blocks(
            Describe.Lean(DescribeId.Create("canonical-two-cut-scalar-summable"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sewing/CanonicalTwoCutScalar.canonical_two_cut_summable"),
                H("Unrestricted canonical two-cut absolute summability"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every lattice D, four integral charges alpha, beta, gamma, delta, five external oscillator polynomials u, v, t, w, p, three signed offsets r, s, k and complex q1, q2 of norm below one, the sum over all occupation pairs (d,e) of the norm of the entire canonical product converges. The factors are q1^level(d) q2^level(e), H(p, canonical(alpha,beta+(gamma+delta),u,r+level(d),b(d))), the d coefficient of canonical(beta,gamma+delta,v,s+level(e)-level(d),b(e)), and the e coefficient of canonical(gamma,delta,t,k-level(e),w). All canonical maps, monomial states and H are the original ones.")),
                    Paragraph(Text("The closed mixed descendant invariant from CanonicalTwoCutOccupation supplies uniform control of the middle coefficient. The original row bound controls the outer coefficient for fixed test occupation P; the original column bound controls the inner coefficient for fixed input W. The constants from those two ends multiply the unrestricted mixed pair estimate. Expanding the five finite external supports then gives the stated polynomial scope.")),
                    Paragraph(Text("The finite overlap has shared occupation u, with d=u+v and e=u+w. Multiplication by the original column factorial envelope cancels binomial(e,u) against the input multiplicity factorials. The resulting three factors are factorialEnvelope(L B,u), factorialEnvelope(L A,v) and factorialEnvelope(B T,w), with radial factors (rho1 rho2)^level(u), rho1^level(v) and rho2^level(w). The radii rho_i=(1+norm(q_i))/2 absorb the explicit energy polynomials. Existing factorial occupation summability and finite-fiber grouping prove convergence without a restriction involving L B norm(q1 q2).")),
                    Paragraph(Text("Both zero parameters are included with the convention 0^0=1; neither is divided out. The two inverse factorial coordinate factors have already canceled into the literal d and e coefficients. No inverse Gram, positivity, nonsingularity, homogeneous-state, fixed internal occupation or vacuum hypothesis is added. The factorial form is coordinate resolution and is not asserted to be an invariant BPZ form.")),
                    Paragraph(Text("The proof uses the lattice vertex-field and normal-product suppliers attributed there to Bakalov--Kac, Matsuo--Nagatomo and Carnahan, together with Mathlib's finite sums and infinite-series calculus. This scalar convergence statement is one analytic sewing component. It does not establish channel transport, operator or Hilbert-space sewing, all-genus CFT coherence, physical realization, the full string or AdS/CFT program, or a claim of literature novelty."))),
                DescribeRole.Theorem)
        )));
}
