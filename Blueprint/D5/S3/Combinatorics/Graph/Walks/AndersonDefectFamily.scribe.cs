using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;
internal sealed class AndersonDefectFamilyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual Anderson defect family has scalar joint commutant and persistent nodal polynomial factors.",
        H("The actual defect family on a cycle"),
        Blocks(
            Paragraph(Text("Let r and m be natural numbers, r at least three and m at least two. Put L=rm and q=(m-1)r+1. The sites are Fin L. The actual sign word U(i) is minus one exactly when i modulo r is zero or i=q, and is one otherwise. Delta is the ordinary cycleGraph L graph Laplacian, equal to 2I minus the cycle adjacency matrix. Put V=diag(U) and H(t)=Delta+tV. The pair in the commutant assertion is Delta,V.")),
            Paragraph(Text("Set T(d)=[[d,-1],[1,0]], a=2+t-lambda, b=2-t-lambda, B_r=T(a)^(r-1)T(b), and sigma_r=trace(B_r). The polynomial Psi_m(s) is the product of s-2cos(2 pi k/m) over integers k satisfying 0<k and 2k<m. Thus traceFactors is exactly Psi_m(sigma_r), with the strict inequality retained.")),
            Paragraph(Text("Write p_t for the actual characteristic polynomial of H(t), and q_t for that of its actual principal submatrix deleting site q. With phi:R[t] to R(t) the coefficient inclusion and T=phi(t), let g be the monic normalized gcd of p_T and q_T over R(t)[lambda]. In the display, p and q without coupling subscripts denote the original bivariate polynomials over R[t][lambda]. For any bivariate polynomial F, F_t means coefficientwise evaluation at the real coupling t. The symbol phi(F) denotes coefficientwise inclusion into R(t)[lambda].")),
            Describe.Lean(DescribeId.Create("anderson-defect-family"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/AndersonDefectFamily.defect_family"),
                H("Scalar joint symmetries and persistent nodal factors"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The first two clauses hold for every m at least two. A complex matrix commuting with both Delta and V is scalar. A real orthogonal matrix commuting with both is I or minus I. These are common commutants of the pair, not commutants of an individual Hamiltonian.")),
                    Paragraph(Text("For m at least three, badness is the original AndersonSymmetryConverseRefutation.bad predicate: at every real coupling, the conjunction of simple spectrum and nonvanishing of every nonzero eigenvector fails. The stronger displayed nodal assertion supplies a real eigenvalue and a nonzero real eigenvector at the same site q for every real t, normalized by z(q+1)=1. No nodal assertion is made for m=2.")),
                    Paragraph(Text("The gcd g is monic and has a monic descent G over R[t][lambda]. This G has a monic divisor of positive degree, so the polynomial nodal factor is nonconstant. It divides both original bivariate characteristic polynomials and remains monic and a common divisor after every real specialization. Every monic irreducible pi dividing the actual trace product divides g; it also has a monic descent F dividing G. The specialization of F remains monic and divides both actual characteristic polynomials at every real t. No exceptional real coupling is removed.")),
                    Paragraph(Text("The algebra proof starts from the actual negative-site projector (I-V)/2. Its adjacency compression has exactly the edge between p=(m-1)r and q=p+1; squaring gives E_pp+E_qq. The positive projector (I+V)/2 sends this pair into the two actual positive runs. Successively removing the preceding frontier yields the sum of their next diagonal units. The run preceding p has length r-1; the run following q has length r-2. At frontier r-1 only the former survives. Its negative neighbour gives an adjacent diagonal unit. The frozen cycle_diagonal_units_full theorem is then applied directly to these actual units; its propagation proof is reused.")),
                    Paragraph(Text("For the nodal construction, periodic transport has block B_r and total monodromy B_r^m. The determinant-one two-by-two Chebyshev formula shows B_r^m=I at each trace value 2cos(2 pi k/m), with 0<2k<m. Choosing an initial state transported to (0,-1) at q produces z(q)=0 and z(q+1)=1. The defect changes a coefficient multiplying zero, so this is an eigenvector of the actual defect Hamiltonian, including the cyclic endpoint equations.")),
                    Paragraph(Text("In an irreducible quotient field AdjoinRoot(pi), a root of the trace product yields this actual eigenvector. It is a root of both the actual characteristic polynomial and the actual deleted-site minor, proving the two divisibilities and hence divisibility by their monic gcd. Integrally closed monic descent and coefficient evaluation are supplied by pinned mathlib. At real couplings, the nonconstant complex discriminant attains an interior trace value; Hermitian spectral theory makes the eigenvalue real, and real parts preserve the normalized eigenvector.")),
                    Paragraph(Text("The construction proves the stated family and factor inclusions. It makes no assertion of general-r irreducibility, equality of g with the trace product, squarefreeness, or a globally analytic eigenpair selection."))),
                DescribeRole.Theorem))));

    private static Formula Call(string n, params Formula[] a) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(n))), [..a]);
    private static Formula Par(Formula x) => Seq(Open,x,Close);
    private static Formula All(string n, Formula t, Formula b) =>
        Seq(Forall,Sp,Par(Seq(F.Id(n),Sp,Colon,Sp,t)),Comma,Sp,b);
    private static Formula Ex(string n, Formula t, Formula b) =>
        Seq(Exists,Sp,Par(Seq(F.Id(n),Sp,Colon,Sp,t)),Comma,Sp,b);
    private static Formula Rel(Formula x, FormulaRelationOperator o, Formula y) =>
        new Formula.Relation(x,o,y);
    private static Formula Equal(Formula x, Formula y) => Rel(x,FormulaRelationOperator.Equal,y);
    private static Formula Logic(Formula x, FormulaLogicOperator o, Formula y) =>
        new Formula.Logic(Par(x),o,Par(y));
    private static Formula And(params Formula[] a)
    {
        Formula f=a[^1];
        for(int i=a.Length-2;i>=0;--i) f=Logic(a[i],FormulaLogicOperator.And,f);
        return f;
    }
    private static Formula Imp(Formula x, Formula y) => Logic(x,FormulaLogicOperator.Implies,y);
    private static Formula Divides(Formula x, Formula y) => Call("Divides",x,y);
    private static Formula Monic(Formula x) => Call("Monic",x);
    private static Formula Statement()
    {
        Formula R=Seq(Mathbb,Grp(F.Id("R"))), C=Seq(Mathbb,Grp(F.Id("C")));
        Formula N=Seq(Mathbb,Grp(F.Id("N"))), r=F.Id("r"), m=F.Id("m");
        Formula t=F.Id("t"), z=F.Id("z"), mu=F.Id("mu"), c=F.Id("c"), X=F.Id("X"), O=F.Id("O");
        Formula sites=Call("Fin",Seq(r,Sp,Cdot,Sp,m));
        Formula matricesR=Call("Matrix",sites,sites,R), matricesC=Call("Matrix",sites,sites,C);
        Formula U=Call("U",r,m), delta=F.Id("Delta"), V=F.Id("V"), I=F.Id("I");
        Formula jointC=All("X",matricesC,Imp(Call("Commute",X,Call("complexify",delta)),
            Imp(Call("Commute",X,Call("complexify",V)),Ex("c",C,Equal(X,Call("smul",c,I))))));
        Formula jointR=All("O",matricesR,Imp(Call("Orthogonal",O),
            Imp(Call("Commute",O,delta),Imp(Call("Commute",O,V),
                Logic(Equal(O,I),FormulaLogicOperator.Or,Equal(O,Seq(Minus,I)))))));
        Formula node=All("t",R,Ex("mu",R,Ex("z",new Formula.TypeArrow(sites,R),And(
            Rel(z,FormulaRelationOperator.NotEqual,D(0)),
            Equal(Call("mulVec",Call("H",t),z),Call("smul",mu,z)),
            Equal(Call("coordinate",z,F.Id("q")),D(0)),
            Equal(Call("coordinate",z,Seq(F.Id("q"),Sp,Plus,Sp,D(1))),D(1))))));
        Formula polyR=Call("Polynomial",R), polyPolyR=Call("Polynomial",polyR);
        Formula polyRat=Call("Polynomial",Call("RatFunc",R));
        Formula G=F.Id("G"), g=F.Id("g"), pi=F.Id("pi"), Q=F.Id("F");
        Formula p=F.Id("p"), q=Seq(F.Id("q"),Underscore,Grp(F.Id("q")));
        Formula specializedG=All("t",R,And(Monic(Call("specialize",G,t)),
            Divides(Call("specialize",G,t),Call("p",t)),
            Divides(Call("specialize",G,t),Call("minor",t))));
        Formula specializedQ=All("t",R,And(Monic(Call("specialize",Q,t)),
            Divides(Call("specialize",Q,t),Call("p",t)),
            Divides(Call("specialize",Q,t),Call("minor",t))));
        Formula factor=All("pi",polyRat,Imp(Monic(pi),Imp(Call("Irreducible",pi),
            Imp(Divides(pi,Call("Psi",m,Call("sigma",r,F.Id("T")))),And(Divides(pi,g),
                Ex("F",polyPolyR,And(Monic(Q),Equal(Call("phi",Q),pi),Divides(Q,G),specializedQ)))))));
        Formula descent=Ex("G",polyPolyR,And(Monic(G),Equal(Call("phi",G),g),
            Divides(G,p),Divides(G,q),specializedG,
            Ex("F",polyPolyR,And(Monic(Q),Rel(D(0),FormulaRelationOperator.LessThan,Call("natDegree",Q)),
                Divides(Q,G))),factor));
        Formula nodalClause=Imp(Rel(D(3),FormulaRelationOperator.LessThanOrEqual,m),
            And(Call("bad",U),node,Monic(g),descent));
        return Disp(All("r",N,All("m",N,
            Imp(Rel(D(3),FormulaRelationOperator.LessThanOrEqual,r),
            Imp(Rel(D(2),FormulaRelationOperator.LessThanOrEqual,m),And(jointC,jointR,nodalClause))))));
    }
}
