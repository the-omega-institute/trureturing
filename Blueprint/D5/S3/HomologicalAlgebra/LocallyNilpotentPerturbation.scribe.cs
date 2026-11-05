using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class LocallyNilpotentPerturbationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Global perturbation inverses and retraction maps with vector-dependent finite inverse polynomials",
        H("Algebraic HPL from pointwise local nilpotence"), Blocks(
            Paragraph(Text("Work over a commutative ring R with R-modules U and V and additive group structures. A FinitePerturbation.Input c consists of endomorphisms d0, h, delta of V and linear maps i : U -> V, p : V -> U. Its hypotheses are d0^2=0, p*i=1, d0*i=0, p*d0=0, d0*h+h*d0=1-i*p, h^2=0, h*i=0, p*h=0, and (d0+delta)^2=0. These are the precise unperturbed contraction and actual perturbed-square assumptions of the generic algebraic result.")),
            Paragraph(Text("Assume pointwise local nilpotence: for every x : V there is n with (h*delta)^n x = 0. The inverse polynomial is sum from j=0 to n-1 of (-h*delta)^j. Each application can use a different n. A global inverse is constructed as an endomorphism unit, which supplies a linear map independently of how cutoffs are chosen. The formulas below connect this inverse back to the finite polynomial on each vector.")),
            Paragraph(Text("Attribution is to the algebraic basic perturbation lemma of Gugenheim--Lambe--Stasheff, Mathlib geometric sums and endomorphism units, and the repository FinitePerturbation algebra. This abstract module supplies the perturbation inference; the lattice consumer separately proves local nilpotence for its original BRST correction.")),
            Describe.Lean(DescribeId.Create("is-unit-one-add-of-locally-nilpotent"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/LocallyNilpotentPerturbation.isUnit_one_add_of_locally_nilpotent"),
                H("A global endomorphism unit from pointwise vanishing"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any a : Module.End R V, the sole additional hypothesis is forall x, exists n, (a^n) x = 0. It implies IsUnit(1+a). This endpoint needs neither U nor an Input c, and imposes no common nilpotence exponent on a.")),
                    Paragraph(Text("The finite geometric identities give S_n(a)((1+a)x)=x and (1+a)(S_n(a)x)=x whenever a^n x=0, where S_n(a)=sum of (-a)^j for j<n. For injectivity, choose the cutoff for x-y and apply its first identity to (1+a)(x-y)=0. For surjectivity at x, choose the cutoff for x and use S_n(a)x as preimage. Mathlib's endomorphism unit/bijection equivalence then produces the global unit. This construction establishes linear invertibility without requiring a globally fixed polynomial."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("k-apply-eq-inverse-polynomial"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/LocallyNilpotentPerturbation.K_apply_eq_inversePolynomial"),
                H("The global K evaluates by any sufficient vector cutoff"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let c have the Input identities above and let nilpotent be the pointwise hypothesis for c.h*c.delta. The definition K is the inverse unit of 1+c.h*c.delta. For x : V and any natural n with ((c.h*c.delta)^n) x = 0, K c nilpotent x = inversePolynomial(c.h*c.delta,n) x.")),
                    Paragraph(Text("The finite polynomial gives a preimage of x under 1+h*delta; applying the genuine inverse K identifies that preimage with Kx. Any sufficient n therefore computes the same value. The statement has no positivity condition on n: at n=0 the vanishing hypothesis is x=0 and the empty polynomial correctly gives zero. In applications a cutoff can be extracted from the finite basis support of x without asserting a uniform endomorphism nilpotence exponent."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("locally-nilpotent-perturbation"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/LocallyNilpotentPerturbation.locally_nilpotent_perturbation"),
                H("All perturbed retraction identities with a computed differential"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For the exact Input and pointwise hypotheses above, put D=d0+delta, K=(1+h*delta)^(-1), J=1-delta*K*h, I=K*i, P=p*J, Hpert=K*h and dU=p*delta*I. The theorem concludes dU^2=0, D*I=I*dU, P*D=dU*P, P*I=1, D*Hpert+Hpert*D=1-I*P, Hpert^2=0, Hpert*I=0 and P*Hpert=0. Square zero of dU and the perturbed retraction are conclusions.")),
                    Paragraph(Text("The unit K and the Jacobson inverse J give two-sided inverses of 1+h*delta and 1+delta*h. With T=delta*K and e=i*p, the noncommutative calculation yields d0*T+T*d0+T*e*T=0 by invertible residual cancellation using D^2=0 and the unperturbed contraction. Composing this identity with p and i gives dU^2=0; the companion identities give both chain maps and the homotopy. The normalized side identities then give the retraction and vanishing composites. The transferred map may be nonzero and is always the defined p*delta*I."))),
                DescribeRole.Theorem))));
}
