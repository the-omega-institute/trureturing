using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class PBActualOuterBudgetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original PB identity and positive two-table readings give both actual outer budgets in a nonzero Clifford fibre. The original response remains total on its original labels.",
        H("Finite budgets for the actual PB outer calls"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-outer-budget"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/PBActualOuterBudget.actual_outer_budget"),
                H("A supporting vector reads the original two outer responses"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("E is the original real Jordan label space and J its bilinear Jordan product. The same total D occurs in PB, in the P2 readout, in the fixed inner output D(x,y), and in both outer calls. The complete BDerivedInterface names the unpaid separate-owner unit rows, all real-angle SO(2) invariance, oddness in both inputs, all real coaxial affine zero values, and square rows. It is a conditional derived interface, not a new raw postulate.")),
                    Paragraph(Text("Readout supplies a real-linear operator reading of every original label, symmetric operators, the original unit, the Jordan multiplication law on the specified known subspace L, and P2 for every vector, including a zero vector. It imposes no multiplication law on unknown outer responses. L contains the unit, x, y and D(x,y), and is closed under J. Fibre supplies represented anticommuting unit axes e,f with op(x)=X e and op(y)=Y f; the same op(D(x,y)) anticommutes with both axes and has square delta squared times the identity. X, Y, lambda and delta may be zero or have either sign; t is nonzero with t squared equal to lambda squared times X squared plus one. The original positive-parameter branch is included.")),
                    Paragraph(Text("The proof constructs a unit supporting vector of the rotated symmetry. For any nonzero starting vector, either its sum with its symmetry image is nonzero, or applying the anticommuting second symmetry gives a nonzero positive-eigenvalue candidate. This construction also retains infinite-dimensional fibres. Its zero expectations give the two Gram budgets by the local Jordan readout law. P2 bounds the two actual unknown outer values separately; PB gives their difference and hence the finite inequality.")),
                    Paragraph(Text("In the displayed statement z=t u+lambda x, nu=D(x,y)-J(x,z), and omega=J(x,y)+D(x,z). These are original labels. Only the operator reading of omega is proved zero. A globally nonzero omega is allowed, and equal readings of the second labels are never used to identify D values. The mathematical supporting vector is a readout, not a preparation, operation, normalized original mass, or physical inverse.")),
                    Paragraph(Text("This is a conditional actual-outer lemma at the readout scope needed by the saturation argument and its scalar-overlap or scalar-square-difference consumer. It does not construct a prescribed-character extension or its nonzero central fibre, discharge the complete B interface, prove the arbitrary original operator-square identity, or close any raw atom. The original C-star representation and static operational bridges retain their own hypotheses. No completion, invertibility, equal-square restriction, D homogeneity, D additivity, quotient descent, or outer-output closure is asserted."))),
                DescribeRole.Theorem))));

    private static Formula I(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] args) => global::StrataLint.Scribe.DefinitionDsl.Call(s,args);
    private static Formula N(int n) => global::StrataLint.Scribe.DefinitionDsl.Num(n);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(s),t,b);
    private static Formula Ex(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(s),t,b);
    private static Formula Eq(Formula a, Formula b) => global::StrataLint.Scribe.DefinitionDsl.Equal(a,b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
        private static Formula And(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Mul(Formula a, Formula b) => global::StrataLint.Scribe.DefinitionDsl.Multiply(a,b);
    private static Formula Add(Formula a, Formula b) => global::StrataLint.Scribe.DefinitionDsl.Add(a,b);
    private static Formula Sub(Formula a, Formula b) => global::StrataLint.Scribe.DefinitionDsl.Subtract(a,b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a,b);
    private static Formula Sq(Formula a) => C("pow",a,N(2));
    private static Formula Conj(params Formula[] xs) => xs.Aggregate(And);
    private static Formula Statement()
    {
        var E=I("E"); var Hh=I("H"); var J=I("J"); var u=I("u"); var d=I("D");
        var l=I("L"); var r=I("R"); var x=I("x"); var y=I("y");
        var X=I("X"); var Y=I("Y"); var delta=I("delta"); var lambda=I("lambda"); var t=I("t"); var v=I("v");
        var real=Seq(Mathbb,Grp(I("R")));
        var z=Add(C("smul",t,u),C("smul",lambda,x));
        var nu=Sub(C("apply",d,x,y),C("apply",J,x,z));
        var omega=Add(C("apply",J,x,y),C("apply",d,x,z));
        Formula Read(Formula a) => C("reading",r,v,a);
        var plus=Read(C("apply",d,Add(y,nu),Add(z,omega)));
        var minus=Read(C("apply",d,Sub(y,nu),Sub(z,omega)));
        var budget=Add(Div(Sq(X),Sq(t)),Sq(delta));
        var result=Ex("v",Hh,Conj(Eq(C("inner",v,v),N(1)),Le(Sq(plus),budget),Le(Sq(minus),budget),
            Eq(Sub(plus,minus),Div(Mul(Mul(Mul(N(2),lambda),Sq(X)),Y),t)),
            Le(Mul(Mul(Sq(lambda),Sq(X)),Sub(Mul(Sq(X),Sq(Y)),Sq(delta))),Add(Sq(X),Sq(delta)))));
        var closed=All("a",E,All("b",E,Imp(And(C("mem",I("a"),l),C("mem",I("b"),l)),C("mem",C("apply",J,I("a"),I("b")),l))));
        var assumptions=Conj(C("PB",J,d),C("BDerivedInterface",J,u,d),C("mem",u,l),closed,
            C("mem",x,l),C("mem",y,l),C("mem",C("apply",d,x,y),l),
            Imp(Eq(t,N(0)),I("False")),Eq(Sq(t),Add(Mul(Sq(lambda),Sq(X)),N(1))),
            C("Nonempty",C("Fibre",r,x,y,X,Y,delta)));
        var body=All("J",C("Bilinear",real,E,E,E),All("u",E,All("D",C("Function",E,E,E),
            All("L",C("Submodule",real,E),All("R",C("Readout",Hh,J,u,d,l),
            All("x",E,All("y",E,All("X",real,All("Y",real,All("delta",real,All("lambda",real,All("t",real,Imp(assumptions,result)))))))))))));
        return All("E",I("Type"),All("H",I("Type"),Seq(
            OpenBracket,C("AddCommGroup",E),CloseBracket,OpenBracket,C("Module",real,E),CloseBracket,
            OpenBracket,C("NormedAddCommGroup",Hh),CloseBracket,OpenBracket,C("InnerProductSpace",real,Hh),CloseBracket,
            OpenBracket,C("Nontrivial",Hh),CloseBracket,body)));
    }
}
