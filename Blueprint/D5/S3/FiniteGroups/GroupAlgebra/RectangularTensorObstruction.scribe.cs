using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.GroupAlgebra;

internal sealed class RectangularTensorObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-field coefficient extraction forces every equivariant composite to have zero trace when the rectangular binomial vanishes.",
        H("The rectangular coefficient obstruction"),
        Blocks(
            Paragraph(Text("Let K be a finite field, q=card K, and G=(K,+). Write V_d=(K[z]_(degree<d))^*, with dual monomial basis e_0,...,e_(d-1). Its actual contragredient action satisfies rho_d(a)e_r(z^s)=choose(s,r)*(-a)^(s-r). This is formula (12) in Elmer and Kadr, DOI 10.1007/s13366-026-00855-9, arXiv:2510.07939v1; the tensor question is Conjecture 3.7(a).")),
            Describe.Lean(
                DescribeId.Create("rectangular-endomorphism-trace"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/RectangularTensorObstruction.endomorphism_trace"),
                H("A single diagonal coordinate determines the trace"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural N with N+2<=q and every G-endomorphism h of V_(N+1), all diagonal coordinates of h in the dual monomial basis agree. In particular trace(h)=(N+1)*h(e_N)(z^N), with N+1 regarded as a scalar in K. This statement imposes no binomial-vanishing hypothesis and includes N=0.")),
                    Paragraph(Text("Use unsigned Hasse coefficient operators A_k, characterized by A_k e_r=choose(r+k,r)*e_(r+k) when r+k<=N, and zero otherwise. The action at -a expands as rho(-a)=sum_(k=0)^N a^k*A_k. Finite-field power sums recover A_k=-sum_(a in K) a^(q-1-k)*rho(-a). The bound N+2<=q makes this extraction valid also for k=0. Consequently every group-equivariant map intertwines the extracted operators. Since A_k e_0=e_k, their triangular coefficients force all diagonal entries of h to agree. This uses the full finite-group action, without requiring any additional torus action."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rectangular-composition-trace-zero"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/RectangularTensorObstruction.composition_trace_zero"),
                H("Every pair of group maps has zero composition trace"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let n,m be any natural numbers with n+m+2<=q and choose(n+m,n)=0 in K. For every pair of G-maps f:V_(n+m+1)->V_(n+1) tensor V_(m+1) and g in the reverse direction, trace(g f)=0. There is no parity condition on n or m and no choice of a preferred inclusion or of a basis for the space of maps.")),
                    Paragraph(Text("Put N=n+m and w=e_n tensor e_m. Let B_k be the unsigned tensor-action coefficients, extracted from the actual action by the same power sums. The image of B_N lies in K*w, B_N(e_0 tensor e_0)=w, and B_m(e_n tensor e_0)=w. The image of A_N is K*e_N. Since g intertwines these operators, the first identity puts g(w) in K*e_N. The last identity makes its e_N coordinate a multiple of choose(N,n), hence zero, so g(w)=0. Likewise f(e_N) lies in K*w. Thus g f has zero top diagonal coordinate, and the constant-diagonal trace formula gives trace(g f)=0.")),
                    Paragraph(Text("No coefficient operator is assumed on an arbitrary relative factor. These operators are extracted only on the specified finite polynomial modules and their tensor. The separate prime-cyclic trace identity handles factors through X tensor M and their retracts."))),
                DescribeRole.Theorem))));
}
