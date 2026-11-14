using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.GroupAlgebra;

internal sealed class ElmerKadrPolynomialCancellationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A polynomial endomorphism's top scalar supplies an invertible block pivot and permits cancellation in the original relative category.",
        H("Polynomial summand cancellation by a scalar pivot"),
        Blocks(
            Paragraph(Text("Let K be a finite field of prime characteristic p, q=card K, and G=(K,+). The Lean type Multiplicative K only writes this additive group multiplicatively. For every natural d put V_d=(K[z]_(degree<d))^*, with the actual signed contragredient action rho_d(alpha)(lambda)(f)=lambda(f(z-alpha)). In particular V_0 is zero. For every natural s, M_(p,s) is the literal direct sum over c in Fin s of V_(p(c+1)). An empty summand set gives M_(p,0)=0.")),
            Paragraph(Text("These are the polynomial actions in formulas (11)--(12) and the relative category of Section 2.2 and Lemma 2.1(iii) in Jonathan Elmer and Kazal Kadr, Some formulae relating modular representations of elementary abelian p-groups, DOI 10.1007/s13366-026-00855-9, arXiv:2510.07939v1. The common-summand step below supplies the cancellation used in the recurrence of their Proof of Corollary 1.3. The scalar-pivot argument is the repository's proof of that step; citing the recurrence does not attribute this formal cancellation theorem or a literature-priority claim to the paper.")),
            Paragraph(Text("For a relative module M, RelativeProjective M P means that P is an actual equivariant retract of X tensor M for some arbitrary representation X. RelativeFactors M f means that f factors as U->P->V through such a P. RelativeStableIso M rho sigma means that there are G-maps F:rho->sigma and G:sigma->rho with G F-id_rho and F G-id_sigma in this ideal. The witnesses P and X have no finite-dimensional restriction. Products of representations below are binary direct sums; they are not tensor products.")),
            Describe.Lean(
                DescribeId.Create("elmer-kadr-original-factor-sandwich"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrPolynomialCancellation.factors_sandwich"),
                H("Changing the outer maps keeps the same relative factor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Over any field K and any group G, let tau be a representation on M and let rho,sigma,rho',sigma' be representations on U,V,W,Z. Given f:rho->sigma with RelativeFactors tau f, l:sigma->sigma' and r:rho'->rho, the composite (l f) r satisfies RelativeFactors tau ((l f) r). K, G and M may have independent universes; U,V,W,Z lie in K's universe as in the original relative definitions. Neither finiteness of K nor a characteristic assumption is needed.")),
                    Paragraph(Text("If f=b a through P, use the identical P, its identical relative-projectivity witness, and the maps a r and l b. The cancellation proof uses this closure property to compress the two inverse errors through the same relative factor."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("elmer-kadr-polynomial-summand-cancellation"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrPolynomialCancellation.polynomial_summand_cancellation"),
                H("Cancel a positive polynomial summand of nonzero characteristic dimension"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every finite field K, prime p with char K=p, natural s,d, and representations rho on A and sigma on B of G=(K,+), assume 0<d, d+1<=q and (d:K) is nonzero. Then RelativeStableIso M_(p,s) (rho direct sum V_d) (sigma direct sum V_d) implies RelativeStableIso M_(p,s) rho sigma. A and B are arbitrary K-modules in K's universe; they need not be finite-dimensional or finitely generated. There is no positivity assumption on s and no restriction on the original relative factors P and X.")),
                    Paragraph(Text("Write e_0,...,e_(d-1) for the dual monomial basis. Finite-field power sums extract all polynomial action coefficients when d+1<=q. An equivariant endomorphism h commutes with these coefficients. They generate e_i from e_0, forcing h to be lower triangular with a constant diagonal and to preserve the top line K e_(d-1). Let lambda(h) be its top diagonal coordinate. Thus lambda is additive and multiplicative, lambda(id)=1, and trace(h)=d*lambda(h). A nonzero lambda(h) makes the triangular determinant nonzero and produces an actual equivariant automorphism with forward map h, together with its actual equivariant inverse.")),
                    Paragraph(Text("The prime-cyclic norm identity for M_(p,s) gives trace(h)=0 whenever h factors through an original relative-projective P. As (d:K) is nonzero, this forces lambda(h)=0. Only the finite-dimensional polynomial target V_d is traced. No trace is taken on A, B, P or X, so this step introduces no hidden finiteness premise.")),
                    Paragraph(Text("Let F:A direct sum V_d -> B direct sum V_d and G in the reverse direction witness the assumed relative relation. Write F in blocks (a,b;c,d0), and write the lower row of G as (gamma,delta). Sandwiching G F-id by the V_d inclusion and projection preserves its relative factor. Applying lambda to that lower-right error gives lambda(gamma b)+lambda(delta)*lambda(d0)=1. If lambda(d0) is nonzero take h=0; otherwise take h=gamma. In either case D=d0+h b has nonzero top scalar, hence an actual equivariant inverse.")),
                    Paragraph(Text("The left shear (y,z)->(y,z+h y) replaces the lower row of F by (c+h a,D). The resulting Schur map S=a-b D^(-1)(c+h a):A->B is equivariant. Put u(x)=(x,-D^(-1)(c+h a)x), v(y)=(y,-h y), w(y,z)=y-b D^(-1)(z+h y), and T=pr_A G v. Direct block identities give T S-id_A=pr_A (G F-id) u and S T-id_B=w (F G-id) v. Both errors therefore factor through the original respective P witnesses. These actual maps establish cancellation without assuming that arbitrary relative witnesses carry extracted polynomial coefficients.")),
                    Paragraph(Text("The substantive step is the scalar-pivot alternative and its actual Schur inverse-error identities, using the polynomial endomorphism structure and the relative trace obstruction together. It supplies cancellation for unrestricted A and B, rather than assuming cancellation as a property of a newly defined quotient."))),
                DescribeRole.Theorem),
            Paragraph(Text("The hypotheses retain characteristic two, s=0 and d=1 whenever the displayed bounds hold. The cancellation theorem assumes d>0, excludes d divisible by p, and requires d<q. It does not assert cancellation for V_q or for arbitrary common modules. The tensor-reflection application treats reflected V_q as a literal relative-projective summand instead of cancelling it.")),
            Paragraph(Text("The declarations express structural existence results, with utility none; no numerical or algorithmic output is claimed. The auxiliary four-slot DependentFamily audit remains unfinished in https://github.com/the-omega-institute/trureturing/issues/30512. In particular the full typed clients, readouts, reconstruction, equivalence, variation, sensitivity and observational dependence have not been validated. This exposition makes no declared_validated claim.")))));
}
