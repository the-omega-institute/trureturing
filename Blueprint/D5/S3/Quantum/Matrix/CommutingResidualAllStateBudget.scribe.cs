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
            NonsingularPencilStateBudgetExposition.Pencil(),
            NonsingularPencilStateBudgetExposition.Budget(),
            Entry("witness","The same table for every positive functional",Witness(),
                "Work in M4(Complex). Set eta=(1−i)/sqrt(2), h=diag(1,1,−1,−1), c=diag(1,−1,−1,1), r=c/16. "
                + "The rows of x are (1,0,1,eta), (0,−1,eta,1), (1,conj(eta),−1,0), (conj(eta),1,0,1). "
                + "Set z=(x−hxh)/2, k=hc, t=ihz, g=t+r, and J(a,b)=(ab+ba)/2. "
                + "The central self-adjoint involution is the unit matrix. The displayed h(),x(),r(),c(),z(),k(),t(),g() denote precisely these constants. "
                + "Every positive complex-linear functional on this same algebra has real readings on x²,k,g. "
                + "For mass m=Re phi(I)>0 its original readings satisfy the homogeneous strict budget. "
                + "In particular every normalized state satisfies Re phi(g)²+Re phi(k)²<Re phi(x²). "
                + "At mass zero the functional is zero and the non-strict budget is equality. "
                + "Direct multiplication also gives r²=J(z,r)²=I/256, so neither residual vanishes. "
                + "For P(p,q)=x²+(p²+q²)I−2pk−2qg and f(w)=w⁴+2w²+3, direct expansion gives "
                + "det P=|f(p−iq)|²+4q²−(q²/32)((p²+q²+3)²+4p²+2)+q⁴/4096. "
                + "Put s=p²+q². When s≤6 the parenthesized coefficient is at most 107; the q=0 branch uses f(p)>0. "
                + "When s≥6, the reverse triangle inequality gives |f(p−iq)|≥s²/2, while (s+3)²+4p²+2≤3s². "
                + "These estimates give det P>0 for every real p,q. The identity det x=3 gives positive definiteness of x², "
                + "and the connected-family bridge turns this nonvanishing determinant into positive definiteness of every P(p,q).",DescribeRole.Theorem),
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
    private static Formula Scale(byte denominator,Formula a)=>Call("smul",new Formula.Fraction(D(1),D(denominator)),a);
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

internal static class NonsingularPencilStateBudgetExposition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/CommutingResidualAllStateBudget.";

    public static DocumentBlock Pencil() =>
        Describe.Lean(DescribeId.Create("nonsingular-pencil"),
                DeclarationHandle.Create(Prefix + "pencil"), H("The two-parameter pencil"),
                StatementSource.FromAuthor(Disp(PencilDefinition())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For finite square complex matrices E,K,G and real parameters p,q, "
                    + "P(E,K,G,p,q)=E+(p²+q²)I−2pK−2qG. All factors and every reading belong to the same matrix algebra."))),
                DescribeRole.Definition);

    public static DocumentBlock Budget() =>
        Describe.Lean(DescribeId.Create("nonsingular-pencil-state-budget"),
                DeclarationHandle.Create(Prefix + "strict_budget"), H("Every positive functional, with its original mass"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume E is positive definite, K and G are Hermitian, and the determinant "
                        + "of P(E,K,G,p,q) is nonzero for every real p,q. Every positive complex-linear functional phi "
                        + "has real readings on E,K,G. If m=Re phi(I)>0, then Re phi(G)²+Re phi(K)²<m Re phi(E). "
                        + "If m=0, phi is the zero functional and the corresponding non-strict budget is equality. "
                        + "No normalization, density-matrix representation, or restriction of the functional family is imposed.")),
                    Paragraph(Text("The positive-definite locus of a continuous Hermitian family is open. "
                        + "When its determinant never vanishes it agrees with the positive-semidefinite locus, which is closed. "
                        + "The real parameter plane is connected and P(E,K,G,0,0)=E, so every pencil value is positive definite. "
                        + "A positive definite matrix dominates a positive scalar multiple of the unit. "
                        + "Apply the original positive functional at p=Re phi(K)/m and q=Re phi(G)/m. "
                        + "The operator norm of a positive functional is its unit value, which also proves the zero-mass assertion.")),
                    Paragraph(Text("The compact-sphere openness argument is adapted from TauCetiProject/TauCeti, "
                        + "commit 8c1eaed7cd02e6fee2db1f66783fb8f03025d76d, TauCeti/Analysis/Matrix/PosDef.lean. "
                        + "The spectral, connectedness, and positive-functional ingredients are classical. "
                        + "This theorem supplies a conditional bridge. The fixed table establishes "
                        + "the nonvanishing determinant on the entire real plane and positivity of E. "
                        + "It does not establish a total response, a complete PB family, or physical source contracts."))),
                DescribeRole.Theorem);

    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] a) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. a]);
    private static Formula Apply(Formula f, Formula a) => new Formula.Apply(f, [a]);
    private static Formula All(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Instance(Formula t, Formula b) => Seq(OpenBracket,t,CloseBracket,Sp,b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Sub(Formula a, Formula b) => Subtract(a,b);
    private static Formula Square(Formula a) => new Formula.Power(a,D(2));
    private static Formula Real => Call("Real");
    private static Formula Mat => Call("Matrix",V("n"),V("n"),Call("Complex"));
    private static Formula One => Call("one",Mat);
    private static Formula Reading(string a) => Call("re",Apply(V("phi"),a=="I"?One:V(a)));
    private static Formula Sum => Add(Square(Reading("G")),Square(Reading("K")));
    private static Formula Bound => Mul(Reading("I"),Reading("E"));
    private static Formula WithIndex(Formula b) => All("n",Seq(Call("Type"),Star),
        Instance(Call("Fintype",V("n")),Instance(Call("DecidableEq",V("n")),b)));
    private static Formula WithMatrices(Formula b) => All("E",Mat,All("K",Mat,All("G",Mat,b)));
    private static Formula P => Call("pencil",V("E"),V("K"),V("G"),V("p"),V("q"));

    private static Formula PencilDefinition() => WithIndex(WithMatrices(All("p",Real,All("q",Real,
        Equal(P,Sub(Sub(Add(V("E"),Call("smul",Add(Square(V("p")),Square(V("q"))),One)),
            Call("smul",Mul(D(2),V("p")),V("K"))),Call("smul",Mul(D(2),V("q")),V("G"))))))));

    private static Formula Statement()
    {
        var readings = And(Equal(Call("im",Apply(V("phi"),V("E"))),D(0)),
            And(Equal(Call("im",Apply(V("phi"),V("K"))),D(0)),
                Equal(Call("im",Apply(V("phi"),V("G"))),D(0))));
        var positive = Imp(new Formula.Relation(D(0),FormulaRelationOperator.LessThan,Reading("I")),
            new Formula.Relation(Sum,FormulaRelationOperator.LessThan,Bound));
        var zero = Imp(Equal(Reading("I"),D(0)),And(Equal(V("phi"),D(0)),Equal(Sum,Bound)));
        var nonzero = All("p",Real,All("q",Real,
            new Formula.Relation(Call("det",P),FormulaRelationOperator.NotEqual,D(0))));
        return WithIndex(WithMatrices(Imp(Call("PosDef",V("E")),Imp(Call("IsHermitian",V("K")),
            Imp(Call("IsHermitian",V("G")),Imp(nonzero,
                All("phi",Call("PositiveLinearMap",Call("Complex"),Mat,Call("Complex")),
                    And(readings,And(positive,zero)))))))));
    }
}
