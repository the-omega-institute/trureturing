using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class CommutingResidualAllStateBudgetDocument : IScribeDocumentDefinition
{
    private const string Prefix="D5/S3/Quantum/Matrix/CommutingResidualAllStateBudget.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A four-dimensional matrix table has a nonzero commuting residual under every positive-state budget.",
        H("A commuting residual with a strict budget for every state"), Blocks(
            Entry("witness","The same table for every positive functional",Witness(),
                "Work in M4(Complex). Set eta=(1−i)/sqrt(2), h=diag(1,1,−1,−1), c=diag(1,−1,−1,1), r=c/16. "
                + "The rows of x are (1,0,1,eta), (0,−1,eta,1), (1,conj(eta),−1,0), (conj(eta),1,0,1). "
                + "Set z=(x−hxh)/2, k=hc, t=ihz, g=t+r, and J(a,b)=(ab+ba)/2. "
                + "The central self-adjoint involution is the unit matrix. The displayed h(),x(),r(),c(),z(),k(),t(),g() denote precisely these constants. "
                + "Every positive complex-linear functional on this same algebra has real readings on x²,k,g. "
                + "For mass m=Re phi(I)>0 its original readings satisfy the homogeneous strict budget. "
                + "In particular every normalized state satisfies Re phi(g)²+Re phi(k)²<Re phi(x²). "
                + "At mass zero the functional is zero and the non-strict budget is equality. "
                + "Direct multiplication also gives r²=J(z,r)²=I/256, so neither residual vanishes.",DescribeRole.Theorem),
            Entry("claim","The zero-residual implication",Claim(),
                "The assertion quantifies over all Hermitian H,X,R in the same four-dimensional algebra, with H²=I. "
                + "Even(H,X)=(X+HXH)/2, J(H,X)=(HX+XH)/2 and Response(H,X,R)=(i/2)(HX−XH)+R. "
                + "It asks whether commuting R with both H and Even(H,X), together with the strict budget "
                + "for every normalized positive complex-linear state, forces R=0.",DescribeRole.Definition),
            Entry("result","The implication fails",Seq(Neg,Sp,Call("claim")),
                "The fixed table satisfies every premise and its residual square is I/256. It therefore refutes the zero-residual implication. "
                + "The determinant calculation keeps every noncommutative cross term, and positivity is transported over the entire real parameter plane. "
                + "This is a fixed-table subsystem refutation. It asserts neither a total original response D nor a complete PB countermodel. "
                + "The seven external contracts remain outside the conclusion: Hilbert preparations; Born masses and complete menus; correlated tensor sources; "
                + "CP/Kraus maps and recursive references; whole instruments and environment outputs; histories, returns and counting; dynamics, clocks, energy and common positive hbar. "
                + "The construction and its synthesis are repository-derived; no historical-priority claim is made.",DescribeRole.Theorem))));

    private static DocumentBlock Entry(string name,string title,Formula formula,string prose,DescribeRole role) =>
        Describe.Lean(DescribeId.Create("commuting-residual-"+name),DeclarationHandle.Create(Prefix+name),H(title),
            StatementSource.FromAuthor(Disp(formula)),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(prose))),role);
    private static Formula V(string s)=>F.Id(s);
    private static Formula Call(string s,params Formula[] a)=>new Formula.FunctionCall(FormulaIdentifier.Create(s),[..a]);
    private static Formula All(string s,Formula t,Formula b)=>new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(s),t,b);
    private static Formula Apply(Formula f,Formula a)=>new Formula.Apply(f,[a]);
    private static Formula And(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Imp(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Add(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Mul(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Sq(Formula a)=>new Formula.Power(a,D(2));
    private static Formula Lt(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Mat=>Call("Matrix",Call("Fin",D(4)),Call("Fin",D(4)),Call("Complex"));
    private static Formula One=>Call("one",Mat);
    private static Formula Pos=>Call("PositiveLinearMap",Call("Complex"),Mat,Call("Complex"));
    private static Formula R(Formula a)=>Call("re",Apply(V("phi"),a));
    private static Formula C(string s)=>Call(s);
    private static Formula J(Formula a,Formula b)=>Call("J",a,b);
    private static Formula Scale(int denominator,Formula a)=>Call("smul",new Formula.Fraction(D(1),D(denominator)),a);
    private static Formula Chain(params Formula[] a)
    {var b=a[^1];for(var i=a.Length-2;i>=0;i--)b=And(a[i],b);return b;}
    private static Formula Witness()
    {
        var sum=Add(Sq(R(C("g"))),Sq(R(C("k"))));var bound=Mul(R(One),R(Sq(C("x"))));
        var readings=All("phi",Pos,Chain(Equal(Call("im",Apply(V("phi"),Sq(C("x")))),D(0)),
            Equal(Call("im",Apply(V("phi"),C("k"))),D(0)),Equal(Call("im",Apply(V("phi"),C("g"))),D(0)),
            Imp(Lt(D(0),R(One)),Lt(sum,bound)),Imp(Equal(R(One),D(0)),And(Equal(V("phi"),D(0)),Equal(sum,bound)))));
        return Chain(Call("IsHermitian",C("h")),Call("IsHermitian",C("x")),Call("IsHermitian",C("r")),
            Equal(Sq(C("h")),One),Equal(C("c"),Scale(2,Add(C("x"),Mul(Mul(C("h"),C("x")),C("h"))))),
            Equal(C("k"),J(C("h"),C("x"))),Equal(C("t"),Call("smul",new Formula.Fraction(Call("Icomplex"),D(2)),
                Subtract(Mul(C("h"),C("x")),Mul(C("x"),C("h"))))),
            Equal(Mul(C("h"),C("r")),Mul(C("r"),C("h"))),Equal(Mul(C("c"),C("r")),Mul(C("r"),C("c"))),
            Equal(Sq(C("r")),Call("smul",new Formula.Fraction(D(1),D(2,5,6)),One)),
            Equal(Sq(J(C("z"),C("r"))),Call("smul",new Formula.Fraction(D(1),D(2,5,6)),One)),readings);
    }
    private static Formula Claim()
    {
        var H=V("H");var X=V("X");var Q=V("R");
        var budget=All("phi",Pos,Imp(Equal(Apply(V("phi"),One),D(1)),
            Lt(Add(Sq(R(Call("Response",H,X,Q))),Sq(R(J(H,X)))),R(Sq(X)))));
        return All("H",Mat,All("X",Mat,All("R",Mat,Imp(Call("IsHermitian",H),Imp(Call("IsHermitian",X),
            Imp(Call("IsHermitian",Q),Imp(Equal(Sq(H),One),Imp(Equal(Mul(H,Q),Mul(Q,H)),
                Imp(Equal(Mul(Call("Even",H,X),Q),Mul(Q,Call("Even",H,X))),Imp(budget,Equal(Q,D(0))))))))))));
    }
}
