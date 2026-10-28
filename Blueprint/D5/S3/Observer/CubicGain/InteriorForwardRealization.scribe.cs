using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CubicGain;

internal sealed class InteriorForwardRealizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All admitted first endpoints and parameter tuples produce one cumulative native history.",
        H("Forward realization of every admitted interior tuple"),
        Blocks(
            Paragraph(Text("Choose integers x,d,m,n,sigma with d>=1, x>d, gcd(x,d)=1, m,n>=1 and sigma=+1 or -1. Define a=x-md>=1, h=n*(x+d)+sigma, c=x+hd, b=mc-d, Q=1+nd and require gcd(a,b)=1. The first endpoint A is a nonnegative integral matrix with determinant +1 or -1 satisfying A*(a,-b)=(x,d). Its action, integrality, nonnegativity and either determinant sign are explicit hypotheses, rather than consequences of the scalar parameters.")),
            Paragraph(Text("The rank filter is the rank-three condition on X mapping to (tr(A*X)-tr(X),tr(K*A*X)-tr(X),tr(H*K*A*X)-tr(X)), where K=[[1,1],[Q,Q+sigma]] and H=[[0,1],[1,h]]. It remains an independent hypothesis. Positivity, primitive row coordinates and ac+bd=cx-d^2>0 follow from the parameters.")),
            Paragraph(Text("The chronological lowerWord(q) repeats [J,M] exactly q times and has matrix L^q=[[1,0],[q,1]]. The word for K is [M,J]++lowerWord(Q) for sigma=1 and [J,M,J]++lowerWord(Q-1) for sigma=-1. The word for H is [J]++lowerWord(h). Thus their matrices are L^Q*U, L^(Q-1)*U*J and L^h*J, with U=J*M. All exponents are nonnegative.")),
            Paragraph(Text("AdmittedTuple(x,d,m,n,sigma,A) is precisely the integer, positivity, coprimality, A-entry, determinant, first-action and rank-three hypotheses above. Realizes(w,p,x,d,m,n,sigma,A) means all four exact primitive coordinate identifications, b,c,h>0, Q>=2, the exact first endpoint, both multiplier matrices, all three explicit word conditions and all four unchanged-index lattice equations, together with OrientedKernelGenerator and ParameterForm on w. PhysicalRun(w,S,f,ell) means positive factors S=f*ell, strict positivity after every finite native word, and the displayed reading identity for every real k,delta and every original index i=0,1,2,3. All abbreviations include their whole stated conjunction; none drops a filter.")),
            Describe.Lean(DescribeId.Create("interiorforwardrealization-admitted-parameters-realize"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/InteriorForwardRealization.admitted_parameters_realize"),
                H("Admitted tuples give the original kernel and actual source runs"), StatementSource.FromAuthor(Disp(Seq(Forall,Sp,F.Id("x"),Comma,F.Id("d"),Comma,F.Id("m"),Comma,F.Id("n"),Comma,F.Id("sigma"),Comma,F.Id("A"),Comma,Sp,C("AdmittedTuple",F.Id("x"),F.Id("d"),F.Id("m"),F.Id("n"),F.Id("sigma"),F.Id("A")),Implies,Sp,Exists,Sp,F.Id("w"),Comma,F.Id("p"),Comma,Sp,C("Realizes",F.Id("w"),F.Id("p"),F.Id("x"),F.Id("d"),F.Id("m"),F.Id("n"),F.Id("sigma"),F.Id("A")),Land,Open,Forall,Sp,F.Id("S"),Comma,C("PositiveRankOne",F.Id("S")),Implies,Sp,Exists,Sp,F.Id("f"),Comma,F.Id("ell"),Comma,C("PhysicalRun",F.Id("w"),F.Id("S"),F.Id("f"),F.Id("ell")),Close))), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Every tuple and first endpoint satisfying the preceding conditions have positive b,c,h and Q>=2. There exist one original chronological word triple w and primitive coordinates p exactly equal to (a,b,c,d). Its first endpoint is A and its next two multipliers are precisely K,H. At all four original indices the signed images are f, f+m*r, f+(m+1)*r, f+(m+1+h)*r. The kernel is exactly the line of F(p), with rank one and strict positive determinant polar on every actual positive rank-one source. ParameterForm holds on these same words.")),
                    Paragraph(Text("A word for A comes from the legal monoid theorem. Append the explicit words for K,H without adding readings. The three displayed signed images have the same ell level. The primitive-lattice converse uses the retained rank-three filter to identify the entire kernel line and its fixed positive polar sign.")),
                    Paragraph(Text("For every strictly positive rank-one real source S on these very words, positive factors fplus and ellplus satisfy S=fplus*ellplus. The row ellplus remains fixed. Every finite forward word, hence every unread prefix of this cumulative execution, keeps the column strictly positive. At every unchanged recorded index i and for every real slope k and whole constant drift delta, (1+i*k)*ellplus*Ai*fplus+delta=(1+i*k)*tr(Ai*S)+delta. Negative slopes and erased gains are included. The positive factorization is reused from the existing full common-source factorization result; the signed kernel column is not used as a physical source.")),
                    Paragraph(Text("The arithmetic classification of all first endpoints and the final-word rank classification are separate questions. No universal positive intersection, source multiplicity or sharper read bound follows from this construction.")))))));
    private static Formula C(string name, params Formula[] args) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, Seq(args), Close);

}
