using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.GroupAlgebra;

internal sealed class ElmerKadrResidueCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite-field relative tensor criterion separates zero low residues from carries in the high indices.",
        H("Residues, tensor splitting and base-p carries"),
        Blocks(
            Paragraph(Text("For a field K, write P_n=K[z]_(degree<=n) and V_d=(K[z]_(degree<d))^*. Translations act on primal polynomials by f(z)->f(z+a); on V_d they act by lambda->(f->lambda(f(z-a))). These are the symmetric-power and contragredient models of Elmer and Kadr, DOI 10.1007/s13366-026-00855-9, arXiv:2510.07939v1, formulas (11)--(12). The relative-projectivity convention is Section 2.2 and Lemma 2.1(iii).")),

            Paragraph(Text("Elmer and Kadr, Some formulae relating modular representations of elementary abelian p-groups, DOI 10.1007/s13366-026-00855-9, arXiv:2510.07939v1, Conjecture 3.7(a), propose a relative tensor formula. The objects here use their polynomial models in formulas (11)--(12) and their relative category in Section 2.2 and Lemma 2.1(iii). The group is the additive group of a finite field K; its multiplicative type notation does not mean K's multiplicative group.")),
            Paragraph(Text("Let K be a finite field, p prime, char K=p and q=card K. For every natural d, V_d=(K[z]_(degree<d))^*, with action rho_d(alpha)(lambda)(f)=lambda(f(z-alpha)); V_0 is the zero module. Take natural a,b,u,v with u<p, v<p, u+v<=p, and put i=pa+u, j=pb+v. Assume i+j<=q. Let M be the literal direct sum over c in Fin(q/p) of V_(p(c+1)), namely V_p,V_(2p),...,V_q. Put t=min(u,v), S=the direct sum over ell in Fin t of V_(i+j-(2ell+1)), and T=V_i tensor V_j, all with their actual direct-sum or diagonal tensor actions. The Fin t indices start at zero; equivalently S has summands V_(i+j-(2r-1)) for r=1,...,t. In particular S is an empty direct sum when t=0.")),
            Paragraph(Text("An M-relatively projective module P is an equivariant retract of X tensor M for some arbitrary representation X. A map belongs to the relative ideal when it factors through such a P. RelativeStableIso M S T means that there are G-maps f:S->T and g:T->S for which g f-id_S and f g-id_T belong to this ideal. The existential modules P and X have no finite-dimensional restriction. This is the inverse-morphism relation in the original relative quotient category.")),
            Describe.Lean(
                DescribeId.Create("elmer-kadr-all-residue-binomial-criterion"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrResidueCriterion.residue_criterion_all"),
                H("Zero low residues or a nonzero high binomial"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every finite field K of prime characteristic p and all natural a,b,u,v satisfying u<p, v<p, u+v<=p and (pa+u)+(pb+v)<=card K, the original relative relation satisfies RelativeStableIso M S T if and only if u=0 or v=0 or choose(a+b,a) is nonzero in K. Here M, S and T are exactly the direct-sum and tensor representations above, with t=min(u,v). There is no positivity assumption on a,b,u,v.")),
                    Paragraph(Text("When either low residue is zero, S is empty and T is relatively projective, independently of the high binomial. When both are nonzero, that binomial is the exact condition. The statement retains a=0, b=0, zero spaces, p=2, u+v=p and equality in the size bound; the relative factors P and their ambient tensor witnesses X remain arbitrary representations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("elmer-kadr-all-residue-no-carry-criterion"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrResidueCriterion.residue_criterion"),
                H("The exact no-carry union"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Under exactly the same hypotheses on the finite field K, p and the natural numbers a,b,u,v, RelativeStableIso M S T holds if and only if u=0 or v=0 or, for every k in Finset.Ico 1 (Nat.log p (a+b)+1), a mod p^k + b mod p^k < p^k. Thus the last alternative tests every integer k from 1 through Nat.log p (a+b), with the upper endpoint of Ico excluded. It is the absence of carries in the base-p addition of the high parts a and b.")),
                    Paragraph(Text("The quantified interval is empty when a+b=0, and also when 0<a+b<p. Either zero low residue makes the union true without a no-carry condition. Lucas's nonvanishing criterion and Kummer's valuation formula replace the high binomial by this exact arithmetic condition; they leave M, the Fin(min u v) direct sum S, T and the relative category unchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("elmer-kadr-residue-decomposition"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrResidueCriterion.residue_decomposition"),
                H("The full direct sum splits off"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Over any field K of prime characteristic p, let a,b,u,v be natural numbers with 1<=u, 1<=v, u+v<=p and choose(a+b,a) nonzero in K. Put i=pa+u, j=pb+v and t=min(u,v). There is an actual equivariant isomorphism V_i tensor V_j congruent to S direct sum (V_(i-t) tensor V_(j-t)), where S is precisely the finite direct sum defined above. This decomposition needs no cardinality bound and no finiteness assumption on K.")),
                    Paragraph(Text("At step h, for 0<=h<t, the one-step polynomial section has scalar choose(i+j-2-2h,i-1-h). Lucas's congruence in characteristic p identifies it with choose(u+v-2-2h,u-1-h)*choose(a+b,a). The first factor is nonzero because its upper index is less than p. Thus the same high binomial makes every step invertible. Iterating the actual split maps removes V_(i+j-1), then V_(i+j-3), and so on, leaving the literal tensor V_(i-t) tensor V_(j-t). The complement inclusions have positive signs; the inverse error on the original tensor is minus its remainder projection."))),
                DescribeRole.Theorem),
            Paragraph(Text("For the finite-field relative statement, one remaining factor has dimension pa or pb. If that dimension is positive, the corresponding V_(pa) or V_(pb) is a specified summand of M; tensoring its inclusion and projection makes the remainder relatively projective. If the dimension is zero, the remainder is zero. The size bound i+j<=q supplies a,b<=q/p. The actual decomposition therefore gives inverse maps modulo precisely the original relative ideal.")),
            Paragraph(Text("If u=0, then t=0, S is genuinely empty, and T has the factor V_(pa). For a>0 this is one of M's literal summands, while a=0 makes T zero. The same argument applies when v=0, using V_(pb) and the tensor flip. The zero maps between S and T give the relative inverse relations because T is relatively projective. These branches impose no condition on carries in a+b.")),
            Paragraph(Text("Conversely suppose u,v>0 and choose(a+b,a)=0 in K. The first summand U=V_(i+j-1) is an actual retract of S. Lucas's congruence gives choose(i+j-2,i-1)=0, so the rectangular coefficient obstruction forces trace(g_U f_U)=0 for every pair of G-maps U->T->U. The dimension of U has characteristic residue u+v-1, between 1 and p-1, so trace(id_U) is nonzero. Sandwiching g f-id_S by the first-summand inclusion and projection retains its same relative factor P. The prime-cyclic norm forces this sandwiched error to have trace zero, whereas its trace is -trace(id_U), a contradiction. This argument uses the retract inside the full S; it does not infer that U itself is relatively stably isomorphic to T.")),
            Paragraph(Text("Lucas's theorem and Kummer's valuation formula identify nonvanishing of choose(a+b,a) with the absence of base-p carries. Two numerical consequences illustrate the distinction. If q<=p^2 and u,v>0, the size bound forces a+b<=p-1, so the high addition has no carry. On the other hand, for q=p^3, a=1, b=p-1 and u=v=1 give i=p+1, j=p^2-p+1 and i+j=p^2+2<=p^3 for every prime p, including p=2. The high binomial is choose(p,1)=p=0 in K, so the relative stable relation fails. At p=3 this uniform rank-three family has i=4, j=7 and a=1, b=2. These are deductions from the displayed criterion.")),
            Paragraph(Text("The characteristic-three example over F_27 with i=j=7 instead has a=b=2 and u=v=1. Its high binomial choose(4,2)=6 vanishes, giving the same obstruction. The classification stated here is confined to the additive group of the finite field K.")))));
}
