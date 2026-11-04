using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;

internal sealed class NativeThirteenHoleRealizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeThirteenHoleRealization", H("Correlated finite realizations of the thirteen-hole rows"), Blocks(
            Describe.Lean(DescribeId.Create("thirteen-hole-guard"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeThirteenHoleRealization.G"),
                H("The guarded finite constructor"),
                StatementSource.FromAuthor(Disp(All("x,t",V("Source"),EqOf(Call("G",V("x"),V("t")),
                    Call("pair",V("x"),Call("pair",Call("substitution",V("t")),Call("of",V("true")))))))),
                AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("The constructor has two original pair levels. Its recursive argument is transformed by the native substitution, while its rightmost child is the original alpha leaf. The finite tail at parameters x, n and m is the n-fold iterate of this constructor on comb(m). The existing comb has comb(0)=alpha and comb(m+1)=pair(comb(m),alpha)."))),DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("thirteen-hole-canonical"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeThirteenHoleRealization.K"),
                H("One canonical guarded completion"),
                StatementSource.FromAuthor(Disp(EqOf(V("K"),Call("at",Call("canonicalSolution",V("system"),Call("constant",V("false")),Call("constant",D(0))),D(0))))),
                AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("The exact one-coordinate functional system has expression pair(token(0,0),pair(var(1,0),ground(alpha))). Its token has the divergent mode and hence denotes Omega. The supplied symbolic_finite_forcing solution law gives K=node(Omega,node(rho(K),alpha)). This defines the particular canonical tree used here; no standalone theorem named K is assumed. Lambda is the ordered thirteen-hole comb with ten copies of Omega followed by three copies of this same K."))),DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("thirteen-hole-theta"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeThirteenHoleRealization.theta"),
                H("Two fillings of the same finite tuple"),
                StatementSource.FromAuthor(Disp(All("s",V("Bool"),All("h",V("Nat"),EqOf(Call("theta",V("s"),V("h")),Call("B",D(1,2),Call("values",V("s"),V("h")))))))),
                AssessedProvenance.FromRepo(),Blocks(
                    Paragraph(Text("At a supplied h put a=2(h+1) and n=h+1. The shared tuple is x=rho^a(comb(1)), y=rho^(a+3)(comb(1)), z=rho^(a+6)(comb(1)), w=rho^(a+9)(comb(1)), v=G(x)^n(comb(4)). The ten-value table is x,y,z,w,rho(x),rho(y),pair(y,z),pair(x,w),v,G(x,v). Both rows use exactly this table. The false-side class map is [0,1,2,3,4,5,4,5,6,7,8,8,9]; the true-side map is [0,1,2,3,6,7,4,5,6,7,8,9,9]. Thus the false side fills s=rho(x),t=rho(y),c=v, and the true side fills s=pair(y,z),t=pair(x,w),c=G(x,v), in the same thirteen-hole U.")),
                    Paragraph(Text("The supplied B_T(12), hole(12), locate, hole_locate and locate_eq retain the original comb geometry. Q is the image of all thirteen hole addresses. The row exterior is the entire comb with a distinct address marker at every hole. Its complete partition contains exactly the ordered Q pairs with equal displayed classes, including every diagonal and both orientations of every unordered bit. Original-present transport is used only after the finite source has been proved to reach the original hole."))),DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("thirteen-hole-signed-joint"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeThirteenHoleRealization.SignedJoint"),
                H("Entire acquired input, complete rows and a common completed prefix"),
                StatementSource.FromAuthor(Disp(JointFormula())),AssessedProvenance.FromRepo(),Blocks(
                    Paragraph(Text("Acquired includes the attained complete one-root-hole row. Its literal list contains epoch-zero branch replies at R^j for j=0 through 11, at holes 9,10,13 and at hole 13 followed by R, together with the alpha reply at hole 13 followed by RR. The positive list is exactly (0,q7,1,q1), (0,q8,1,q2), (0,q9L,0,q2), (0,q9R,0,q3), (0,q10L,0,q1), (0,q10R,0,q4), (0,q13L,0,q1), (0,q13RL,1,q11). Every positive retains both reached guards. The negative list ranges over all unordered distinct pairs among holes 1,2,3,4,7,8,9,10,11,13, at epoch zero, with both reached guards.")),
                    Paragraph(Text("The two literalRecord equalities specify the entire comb exterior and every partition bit. All thirteen holes are reached in each source. canonicalRow_record_iff also identifies each canonical row with its attained reference at h=0. The two originals differ because their full partitions differ. Agreement quantifies every address through the inclusive depth, including alpha and beta leaves and absent descendants below early leaves. No equality of cross-source finite feedback is required."))),DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("thirteen-hole-actual-realization"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeThirteenHoleRealization.actual_joint_realization"),
                H("Actual signed finite realizations at every inclusive depth"),
                StatementSource.FromAuthor(Disp(All("h",V("Nat"),Call("SignedJoint",V("h"),Call("theta",V("false"),V("h")),Call("theta",V("true"),V("h")))))),
                AssessedProvenance.FromRepo(),Blocks(
                    Paragraph(Text("The guarded-prefix induction is uniform in prefix depth d, iterate count n, and comb seed m. If x and Omega have the same cutoff d and d is at most 2n, then G(x)^n(comb(m)) and K have the same cutoff d. At positive depth one constructor gives the branch root. At depth d+2 the two original pair levels reduce the recursive comparison to depth d, and the existing native cutoff transport preserves that comparison under rho. The alpha child is exact at every stage. The induction keeps the same x throughout.")),
                    Paragraph(Text("Native iteration through 2(h+1) makes x full to cutoff h+1; the three offset iterates preserve its agreement with Omega. Applying the guarded-prefix induction at n=h+1 gives v the required prefix of K. Pair locality and the exact K equation then give both entire Theta outputs the prefix of the same Lambda. The convention cutoff(h+1) is required for inclusive h.")),
                    Paragraph(Text("Mass distinguishes the six first values, the two pair helpers, and the two guarded values into groups of masses 1, 3, 4+3(h+1), and 4+3(h+2). Within the mass-one group the clocks are a+2,a+5,a+8,a+11,a+3,a+6; the mass-three clocks are a+10,a+13. Thus all ten values are distinct simultaneously. Every negative and all complete row bits follow for the same tuple. All finite outputs are computed by bounded native iteration and the fixed finite comb.")),
                    Paragraph(Text("This establishes the forward actual-realization part of the signed thirteen-hole construction. It makes no claim of reverse classification on arbitrary original sources, uniqueness of a common closure point, non-rationality, a general recognizer, extraction algorithm, or resource bound."))),DescribeRole.Theorem)
        )));

    private static Formula JointFormula()
    {
        var h=V("h");var u=V("u");var v=V("v");var p=V("p");var i=V("i");
        Formula At(Formula t)=>Call("subtree",Call("position",i),t);
        var reached=All("i",Call("Fin",D(1,3)),AndOf(Call("isSome",At(u)),Call("isSome",At(v))));
        var pref=All("p",V("Address"),Imp(Seq(Call("length",p),Sp,Le,Sp,h),AndOf(
            EqOf(Call("readout",p,u),Call("completionReadout",p,V("Lambda"))),
            EqOf(Call("readout",p,v),Call("completionReadout",p,V("Lambda"))))));
        var body=AndOf(Call("Acquired",u),Call("Acquired",v),
            EqOf(Call("literalRecord",V("Q"),u),Call("row",V("false"))),
            EqOf(Call("literalRecord",V("Q"),v),Call("row",V("true"))),reached,
            EqOf(Call("canonicalRow",V("Q"),u),Call("canonicalRow",V("Q"),Call("theta",V("false"),D(0)))),
            EqOf(Call("canonicalRow",V("Q"),v),Call("canonicalRow",V("Q"),Call("theta",V("true"),D(0)))),
            Seq(u,Sp,Neq,Sp,v),pref);
        return All("h",V("Nat"),All("u,v",V("Source"),IffOf(Call("SignedJoint",h,u,v),body)));
    }
    private static Formula V(string s)=>F.Id(s);
    private static Formula Par(Formula f)=>Seq(Open,f,Close);
    private static Formula Call(string n,params Formula[] xs)=>new Formula.Apply(Seq(Operatorname,Grp(V(n))),[..xs]);
    private static Formula EqOf(Formula a,Formula b)=>Seq(a,Sp,Eq,Sp,b);
    private static Formula IffOf(Formula a,Formula b)=>Seq(Par(a),Sp,Iff,Sp,Par(b));
    private static Formula Imp(Formula a,Formula b)=>Seq(Par(a),Sp,Implies,Sp,Par(b));
    private static Formula AndOf(params Formula[] xs)=>xs.Length==1?xs[0]:Seq(Par(xs[0]),Sp,Land,Sp,Par(AndOf(xs.Skip(1).ToArray())));
    private static Formula All(string ns,Formula t,Formula b)=>Seq(Forall,Sp,Seq(ns.Split(',').Select((n,i)=>i==0?V(n):Seq(Comma,Sp,V(n))).ToArray()),Colon,Sp,t,Comma,Sp,Par(b));
}
