using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.MiddleGap;

internal sealed class ThreeNegativeMiddleGapJointLiftDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A physical floor-mask joint order for strictly ordered middle-minimum gaps",
        H("The complete middle-minimum chamber"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-source-three-negative-middle-gap-joint-lift"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/MiddleGap/ThreeNegativeMiddleGapJointLift.actualSource_three_negative_middle_gap_joint_lift"),
                H("One complete physical permutation and one literal ear cut"), StatementSource.FromAuthor(FullStatement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural a,b,c with 2<=b<a<c, put k=a+b+c and u=1+2^a+2^(a+b). The theorem constructs one list sigma of Fin(k) and a natural j<=k such that OriginalOrder(k,u,sigma) and OriginalOrder(k+1,2u,earWord(k,sigma,j)). Each OriginalOrder includes the complete permutation of all physical labels, an independent integer total zero, and a prefix sum between zero and floor((2^k-1)/2) (respectively floor((2^(k+1)-1)/2)) for every natural take-prefix, including empty and overlong prefixes. No coprimality or unit hypothesis is imposed on either seed. The old labels retain their original identity through castSucc, and the single fresh label k is inserted at the literal cut j.")),
                    Paragraph(Text("Write r=2^a, s=2^b, t=2^c, N=rst-1 and C=(N-1)/2. The old actual source is f(i)=center_N(2^i*u), and the new source is g(i)=center_(2N+1)(2^(i+1)*u). The positive physical labels are U_i=i for i<c-1, V_i=c+i for i<b-1 and W_i=c+b+i for i<a-1. The three negative labels are alpha=c-1, beta=c+b-1 and gamma=k-1. Choose m=floor(C/u). The set P is exactly the U-chain binary mask m, T is exactly the W-chain binary mask r/2-1, and Q is the literal complement of P,T and the three negative labels in range(k). The word is [P,beta,Q,alpha,T,gamma], and j=|P|+1. The bound m<t/2 follows from C<u*t/2, so P fits its chain. The T mask fits its own chain, which is disjoint from P. The physical-inventory lemma proves exhaustiveness and no repeated physical labels. Any fixed internal ordering of each positive block works.")),
                    Paragraph(Text("Put B=1+t+tr and L=1+s+st. The paired positive values are U_i=(u*2^i,2u*2^i), V_i=(B*2^i,(2B-1)*2^i) and W_i=(L*2^i,(2L-s-1)*2^i). The old negative magnitudes are H_alpha=(N-B)/2, H_beta=(N-L)/2 and H_gamma=(N-u)/2. The new magnitudes are K_alpha=2H_alpha+1, K_beta=2H_beta+s/2+1 and K_gamma=2H_gamma+(u+1)/2. The theorem ThreeNegativeMinimumTwoJointLift.paired_chains gives these identities. They follow by applying actual_source_chains at (a,b,c) and at (a,b,c+1), both at the same original seed, followed by the literal index+1 identity. The fresh source g(k)=u follows from centered_full_period. No cyclic relabelling, independent new order or shorter numerical period is used.")),
                    Paragraph(Text("Put G=C-u*floor(C/u) and A=st+s/2-1-2G. Since c>a, either t>=4r or t=2r. In the former case G<=u-1 gives A>=2r(s-1)+s/2-1>0. In the latter case write r=h(s+1)+d with 1<=d<=s. The residue d is nonzero because the odd integer s+1>1 is coprime to every power of two. Exact expansion gives C=u(r-h-1)+r(s-d)+h. Its remainder r(s-d)+h is nonnegative and strictly less than rs, since h<r and d>=1. Therefore G<rs and A>s/2-1>0.")),
                    Paragraph(Text("The mask sums are x=f(P)=um=C-G, g(P)=2x, y=f(T)=(r/2-1)L and g(T)=(r/2-1)(2L-s-1). Thus g(P)-K_beta=A>0. With delta=H_gamma-y=s(t-r)+s-r and D=K_gamma-g(T), one has delta>=0, D=2delta+r(s+1)-s>=0 and N-K_alpha-D=t(r+1-2s)+r(s+1)-s>0. The conditions r>=2s, s>=4 and t>=2r establish the signs. The first new seam implies H_beta<=x<=C; the tail slack implies y<=H_gamma and H_alpha+H_gamma-y<=C. These are the exact old seams. For the new word the fresh positive u begins Q, and the new seams are K_beta<=g(P)<=N and g(T)<=K_gamma with K_alpha+K_gamma-g(T)<=N.")),
                    Paragraph(Text("The source_zero theorem establishes both complete actual integer totals. The complete physical inventory and these totals identify the middle block endpoint from the tail mass. The physical_schedule strip proof controls every interior positive prefix and both endpoints of each negative step. The lift_order and marked_word lemmas transfer this complete natural-label schedule to Fin(k) and to the literal earWord at j.")),
                    Paragraph(Text("This proves the entire strict chamber 2<=b<a<c of the joint-order problem associated with Circle Conjecture 3.1 of Damasdi, Frankl, Pach and Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2. The general paired-chain identities, together with the source, inventory, strip and ear lemmas, suffice for this chamber without assuming the equal-outer or minimum-two endpoint conclusions. This statement does not settle the other gap chambers, the four-gap problem, or the full joint-order problem; full C3.1 remains open."))),
                DescribeRole.Theorem)), []));

    private static Formula FullStatement()
    {
        Formula a = F.Id("a"), b = F.Id("b"), c = F.Id("c");
        Formula sigma = F.Id("sigma"), j = F.Id("j");
        Formula k = Add(Add(a, b), c);
        Formula seed = Add(Add(new Formula.Number(1), Pow(new Formula.Number(2), a)),
            Pow(new Formula.Number(2), Add(a, b)));
        Formula conclusion = Exists("sigma", Call("List", Call("Fin", k)),
            Exists("j", Nat(), And(Le(j, k),
                Call("OriginalOrder", k, seed, sigma),
                Call("OriginalOrder", Add(k, new Formula.Number(1)),
                    Mul(new Formula.Number(2), seed), Call("earWord", k, sigma, j)))));
        Formula statement = Imp(Le(new Formula.Number(2), b),
            Imp(Lt(b, a), Imp(Lt(a, c), conclusion)));
        foreach (var name in new[] { "c", "b", "a" })
            statement = new Formula.Bind(FormulaQuantifier.ForAll,
                FormulaIdentifier.Create(name), Nat(), statement);
        return Disp(statement);
    }

    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(params Formula[] values)
    {
        Formula result = values[^1];
        for (var i = values.Length - 2; i >= 0; i--)
            result = new Formula.Logic(values[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
}
