using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.GroupAlgebra;

internal sealed class PrimeCyclicRelativeTraceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A prime-cyclic conjugation norm on the original relative module forces relative factors to have zero target trace.",
        H("Prime-field norms and relative traces"),
        Blocks(
            Paragraph(Text("Let p be prime and K a field of characteristic p. The group G is the additive group of K, written multiplicatively only as a type convention. Put V_d=(K[z]_(degree<d))^*, with contragredient action rho_d(a)(lambda)(f)=lambda(f(z-a)). For a natural s, M_(p,s) is the literal direct sum of V_p,V_(2p),...,V_(sp). These are the polynomial modules and the relative setting of Elmer and Kadr, DOI 10.1007/s13366-026-00855-9, arXiv:2510.07939v1, formulas (11)--(12), Section 2.2 and Lemma 2.1(iii). K need not be finite for the statements below.")),
            Describe.Lean(
                DescribeId.Create("prime-cyclic-relative-norm"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/PrimeCyclicRelativeTrace.relative_norm"),
                H("A conjugation sum equal to the identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Embed C=(F_p,+) into G by the prime-field inclusion. For every natural s there is an explicit endomorphism t of M_(p,s) such that sum_(c in C) rho_M(c) t rho_M(-c)=id_M. This is an ordinary sum, with no division by p. It includes p=2 and s=0, when the direct sum is the zero space.")),
                    Paragraph(Text("On the primal degree<pr polynomials, use Q_r(z)=(z^p-z)^r and t_r(f)=remainder of -z^(p-1)*f modulo Q_r. The polynomial Q_r is monic of degree pr and fixed by prime-field translations, so translation commutes with taking this remainder. The identity sum_(c in F_p) -(z+c)^(p-1)=1 then makes the conjugation sum of t_r the identity. This also holds for r=0: Q_0=1 and the degree<0 space is zero.")),
                    Paragraph(Text("Transpose t_r to V_(pr). The dual action uses the inverse group element, and transposition reverses composition; reindexing the finite sum by c->-c gives the stated conjugation sum on the dual. Taking the direct sum of these operators gives t on M_(p,s). Both the minus sign in -z^(p-1) and the inverse in the contragredient are part of the calculation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-cyclic-relative-factor-trace"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/PrimeCyclicRelativeTrace.trace_relativeFactors"),
                H("Trace sees through arbitrary relative factors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural s, every K-representation U of G and every equivariant endomorphism h of U which factors through an M_(p,s)-relatively projective module, trace_K(h)=0. Here relatively projective means an actual equivariant retract P of X tensor M_(p,s), with X arbitrary; a factorization of h has maps U->P->U. Neither P nor X is required to be finite-dimensional. The trace operation in the statement is defined for arbitrary U; its application to the classifier uses the ordinary trace on a finite-dimensional U.")),
                    Paragraph(Text("Tensor the norm-one operator on M_(p,s) with id_X. If i:P->X tensor M and r:X tensor M->P have r i=id_P, compose the maps U->P->U with i and r. The norm identity expresses h as a sum of p conjugates of one endomorphism of U. Each conjugate has the same target trace, so trace(h)=p*trace(h0)=0 in characteristic p. Only U is traced: no cyclic permutation of a trace across an arbitrary-dimensional factor is needed."))),
                DescribeRole.Theorem))));
}
