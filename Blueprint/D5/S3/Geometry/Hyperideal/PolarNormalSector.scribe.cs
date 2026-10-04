using System;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class PolarNormalSectorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Forward normal sectors of literal polar edges and their original six-coordinate dihedral angles.",
        H("Polar edges in an algebraic Lorentz frame"),
        Blocks(
            Paragraph(Text("The ambient space E is Real times EuclideanSpace(Real,Fin(3)), with "
                + "lorentz((t,X),(u,Y))=-tu+inner(X,Y). GramFrame consists of an actual basis "
                + "and its actual Lorentz-dual basis, with diagonal Gram entries 1 and "
                + "off-diagonal entries -lengths(i,j), where 1<lengths(i,j)<=2. It includes "
                + "no geometric cell or tangent-metric certificate. Both bases undergo the "
                + "same time reflection when the time coordinate of their primal sum is negative.")),
            Paragraph(Text("For F:GramFrame, e:Perm(Fin(4)), and s:Real, let a(F,e,i) and "
                + "w(F,e,i) be the oriented primal and dual vectors at e(i). Define "
                + "L(F,e)=arcosh(lengths(e(0),e(1))) and d(F,e)=sinh(L(F,e)). "
                + "Put p(F,e,s)=(cosh(L-s)a(F,e,0)+cosh(s)a(F,e,1))/d and "
                + "v(F,e,s)=(-sinh(L-s)a(F,e,0)+sinh(s)a(F,e,1))/d. "
                + "K(F) consists literally of q with lorentz(q,q)=-1, q.time>0, "
                + "lorentz(q,w(F,e,i))>=0 and lorentz(q,a(F,e,i))<=0 for every i; "
                + "this definition is independent of e.")),
            Paragraph(Text("N(F,e,s) is the intersection of the Lorentz orthogonal kernels "
                + "of p and v. For i=2,3, n(F,e,i)=-w(F,e,i)/sqrt(lorentz(w(F,e,i),w(F,e,i))). "
                + "Set c(F,e)=lorentz(n(F,e,2),n(F,e,3)) and eta=sqrt(1-c^2). "
                + "The inward rays are r0(F,e)=(-n(F,e,3)+c*n(F,e,2))/eta and "
                + "r1(F,e)=(-n(F,e,2)+c*n(F,e,3))/eta.")),
            Paragraph(Text("For a unit timelike p, its tangent space carries the norm and "
                + "inner product built from the positive Lorentz restriction, rather than "
                + "the ambient Euclidean norm. The geodesic in direction u is constant p "
                + "when u=0, and otherwise cosh(t*sqrt(lorentz(u,u)))*p plus "
                + "sinh(t*sqrt(lorentz(u,u)))/sqrt(lorentz(u,u))*u. Cforward(F,e,s) "
                + "contains exactly the u in N for which every sufficiently small positive "
                + "time lies in K. angleB denotes InnerProductGeometry.angle in the "
                + "compatible tangent inner-product space. HasDerivAt(edgePoint(F,e),v,s) means "
                + "HasDerivAt of the function t->p(F,e,t), with derivative v(F,e,s), at s. "
                + "time(q) and spatial(q) are the two ambient coordinates; inner is the "
                + "ordinary spatial real inner product; zeroE is the zero vector of E.")),
            Paragraph(Text("G(F,e) is the actual primal Gram matrix in order e(0),e(1),e(2),e(3). "
                + "V(F,e) has rows given by the time and three spatial coordinates of these "
                + "vectors. D(F,e)=-det(G(F,e)). Let the six arguments (x,y,z,o,v,w) be "
                + "(lengths(e(0),e(1)),lengths(e(0),e(2)),lengths(e(0),e(3)), "
                + "lengths(e(2),e(3)),lengths(e(1),e(3)),lengths(e(1),e(2))). "
                + "Define RadA(F,e)=rad(x,y,w), RadB(F,e)=rad(x,z,v), and "
                + "P(F,e)=numerator(x,y,z,o,v,w), using FourCycleEnvelopes: "
                + "rad(x,y,z)=2xyz+x^2+y^2+z^2-1 and "
                + "numerator(x,y,z,o,v,w)=yz+vw+xyv+xzw-(x^2-1)o. "
                + "phi(F,e)=cosine(x,y,z,o,v,w)=P/sqrt(RadA)/sqrt(RadB). "
                + "delta(i,j) is 1 when i=j and 0 otherwise.")),
            Describe.Lean(
                DescribeId.Create("polar-edge-forward-sector"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/PolarNormalSector.polar_edge_forward_sector"),
                H("The actual forward sector and its dihedral angle"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Spatial Cauchy-Schwarz proves the positive tangent form. "
                        + "The common time reflection selects the future sheet, and the exact "
                        + "edge expressions give two active lateral constraints and six strict "
                        + "inactive constraints. Dual-basis coordinates identify the actual "
                        + "two-dimensional normal plane.")),
                    Paragraph(Text("Continuity preserves the inactive constraints near time zero. "
                        + "For a nonzero tangent direction and positive time, the active "
                        + "geodesic coefficient is strictly positive. Thus forward containment "
                        + "is exactly the two normal halfspaces, whose intersection is the "
                        + "nonnegative span of the actual inward rays. The zero direction "
                        + "is included through the constant geodesic.")),
                    Paragraph(Text("The actual coordinate matrix factors the Gram matrix through "
                        + "diag(-1,1,1,1). Adjugate identities yield the swapped dual "
                        + "diagonals RadB/D and RadA/D and cross entry -P/D. Their universal "
                        + "polynomial relation fixes the original edge ordering and sign; "
                        + "the compatible tangent angle is arccos(phi).")),
                    Paragraph(Text("The statement is over actual algebraic Gram frames. "
                        + "Construction for every original six-length input and identification "
                        + "with a canonical marked hyperideal block remain separate obligations. "
                        + "This local theorem gives no global cell, gluing, manifold, curvature "
                        + "or completeness conclusion."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var f=F.Id("F"); var e=F.Id("e"); var s=F.Id("s");
        Formula X(string n) => Call(n,f,e);
        Formula Y(string n) => Call(n,f,e,s);
        Formula A(Formula i) => Call("a",f,e,i);
        Formula W(Formula i) => Call("w",f,e,i);
        Formula N(byte i) => Call("n",f,e,F.D(i));
        var p=Y("p"); var velocity=Y("v"); var r0=X("r0"); var r1=X("r1");
        var u=F.Id("u"); var alpha=F.Id("a"); var beta=F.Id("b");
        var cone=Exists("a",Real,Exists("b",Real,
            And(Le(F.D(0),alpha),Le(F.D(0),beta),Eq(u,Add(Mul(alpha,r0),Mul(beta,r1))))));
        var span=Exists("a",Real,Exists("b",Real,
            Eq(u,Add(Mul(alpha,W(F.D(2))),Mul(beta,W(F.D(3)))))));
        var D=X("D"); var radA=X("RadA"); var radB=X("RadB"); var P=X("P");
        var i=F.Id("i"); var q=F.Id("q"); var h=F.Id("h");
        var fin4=Call("Fin",F.D(4));
        var lateral=All("i",fin4,Eq(B(p,W(i)),Div(Add(
            Mul(Call("cosh",Sub(X("L"),s)),Call("delta",i,F.D(0))),
            Mul(Call("cosh",s),Call("delta",i,F.D(1)))),X("d"))));
        var complement=All("i",fin4,Imp(Or(Eq(i,F.D(2)),Eq(i,F.D(3))),
            Eq(B(p,A(i)),Neg(Div(Add(
                Mul(Call("lengths",f,Call("e",F.D(0)),Call("e",i)),Call("cosh",Sub(X("L"),s))),
                Mul(Call("lengths",f,Call("e",F.D(1)),Call("e",i)),Call("cosh",s))),X("d"))))));
        var metric=All("q",F.Id("E"),All("h",F.Id("E"),Imp(
            And(Eq(B(q,q),Neg(F.D(1))),Eq(B(q,h),F.D(0))),
            And(Le(Call("inner",Call("spatial",h),Call("spatial",h)),
                Mul(Sq(Call("time",q)),B(h,h))),
                Iff(Eq(B(h,h),F.D(0)),Eq(h,Call("zeroE")))))));
        var conclusion=And(
            In(p,Call("K",f)), Eq(B(velocity,velocity),F.D(1)), Eq(B(p,velocity),F.D(0)),
            All("u",F.Id("E"),Iff(In(u,Y("N")),span)),Eq(Call("finrank",Y("N")),F.D(2)),
            All("u",F.Id("E"),Iff(In(u,Y("Cforward")),cone)),
            Eq(B(r0,r0),F.D(1)),Eq(B(r1,r1),F.D(1)),Lt(F.D(0),Sub(F.D(1),Sq(X("c")))),
            And(Lt(F.D(0),D),Eq(D,Sq(Call("det",X("V")))),
                Eq(B(W(F.D(2)),W(F.D(2))),Div(radB,D)),
                Eq(B(W(F.D(3)),W(F.D(3))),Div(radA,D)),
                Eq(B(W(F.D(2)),W(F.D(3))),Div(Neg(P),D)),
                Eq(Sub(Mul(radA,radB),Sq(P)),Mul(Sub(Sq(Call("lengths",f,Call("e",F.D(0)),Call("e",F.D(1)))),F.D(1)),D))),
            metric, Call("HasDerivAt",Call("edgePoint",f,e),velocity,s),
            And(lateral,Eq(B(p,A(F.D(0))),Neg(Call("sinh",s))),
                Eq(B(p,A(F.D(1))),Neg(Call("sinh",Sub(X("L"),s)))),
                All("i",fin4,Lt(B(p,A(i)),F.D(0))),complement),
            All("u",F.Id("E"),Iff(In(u,Y("Cforward")),
                And(In(u,Y("N")),Le(B(u,N(2)),F.D(0)),Le(B(u,N(3)),F.D(0))))),
            Eq(B(r0,r1),X("phi")),
            And(Eq(B(p,p),Neg(F.D(1))),Eq(B(p,r0),F.D(0)),Eq(B(p,r1),F.D(0)),
                Eq(Call("angleB",p,r0,r1),Call("arccos",X("phi")))));
        return All("F",new Formula.NamedConstant(FormulaIdentifier.Create("GramFrame")),All("e",Call("Perm",fin4),All("s",Real,
            Imp(And(Lt(F.D(0),s),Lt(s,X("L"))),conclusion))));
    }
    private static Formula Real => new Formula.NamedConstant(FormulaIdentifier.Create("Real"));
    private static Formula Call(string name,params Formula[] a)=>name == "e" ? new Formula.Apply(F.Id(name),[..a]) : new Formula.FunctionCall(FormulaIdentifier.Create(name),[..a]);
    private static Formula B(Formula x,Formula y)=>Call("lorentz",x,y);
    private static Formula Eq(Formula x,Formula y)=>new Formula.Relation(x,FormulaRelationOperator.Equal,y);
    private static Formula Le(Formula x,Formula y)=>new Formula.Relation(x,FormulaRelationOperator.LessThanOrEqual,y);
    private static Formula Lt(Formula x,Formula y)=>new Formula.Relation(x,FormulaRelationOperator.LessThan,y);
    private static Formula In(Formula x,Formula y)=>new Formula.Relation(x,FormulaRelationOperator.MemberOf,y);
    private static Formula Iff(Formula x,Formula y)=>new Formula.Logic(x,FormulaLogicOperator.Iff,y);
    private static Formula Imp(Formula x,Formula y)=>new Formula.Logic(x,FormulaLogicOperator.Implies,y);
    private static Formula Or(Formula x,Formula y)=>new Formula.Logic(x,FormulaLogicOperator.Or,y);
    private static Formula Add(Formula x,Formula y)=>new Formula.Binary(x,FormulaBinaryOperator.Add,y);
    private static Formula Sub(Formula x,Formula y)=>new Formula.Binary(x,FormulaBinaryOperator.Subtract,y);
    private static Formula Mul(Formula x,Formula y)=>new Formula.Binary(x,FormulaBinaryOperator.Multiply,y);
    private static Formula Div(Formula x,Formula y)=>new Formula.Fraction(x,y);
    private static Formula Neg(Formula x)=>new Formula.Negate(x);
    private static Formula Sq(Formula x)=>new Formula.Power(x,F.D(2));
    private static Formula All(string v,Formula d,Formula b)=>new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(v),d,b);
    private static Formula Exists(string v,Formula d,Formula b)=>new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(v),d,b);
    private static Formula And(params Formula[] a)
    {
        if(a.Length==0)throw new ArgumentException("Empty conjunction");
        var r=a[^1];for(var i=a.Length-2;i>=0;i--)r=new Formula.Logic(a[i],FormulaLogicOperator.And,r);return r;
    }
}
