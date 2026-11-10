using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class BalancedStarRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A single zero probe detects every nonzero real residual in the full balanced three-dimensional star, with an explicit finite positive vector reading.",
        H("Balanced-star rigidity with both environment edges"),
        Blocks(
            Paragraph(Text("The algebra A is Matrix(Fin 3,Fin 3,Complex), with ordinary multiplication, conjugate transpose and the positive semidefinite order. Set P=diag(1,1,0), c=diag(1,2,0), and t=((0,0,1),(0,0,sqrt(2)),(1,sqrt(2),0)). Thus both environment edges, of weights 1 and sqrt(2), are retained. The probe condition CornerSA(x) means star(x)=x and P*x*P=x. The orientation sigma is either 1 or -1, and rho ranges over all real numbers.")),
            Paragraph(Text("Write J(a,b)=(ab+ba)/2, K(sigma,a,b)=(sigma*i/2)(ab-ba), s(rho)=rho*diag(1,-2,0), and g(sigma,rho)=K(sigma,c,t)+s(rho). At a probe x define h=K(sigma,c,x), r=J(c,x), k=J(c,t), Rplus=x+(h-k), Rminus=x-(h-k), Splus=t+(r+g), Sminus=t-(r+g), and L=-2*J(x,h-k)-2*J(t,r+g). Here Rp and Rm denote Rplus and Rminus, and Sp and Sm denote Splus and Sminus. These are the complete original labels.")),
            Paragraph(Text("PositiveFunctionals(A) denotes all positive complex-linear maps from A to Complex. For such a phi put read(phi,a)=Re(phi(a)) and B(phi,a,b)=read(phi,a*a)*read(phi,b*b)-read(phi,J(a,b)) squared. Selfadjoint readings are real and B is nonnegative for selfadjoint a,b, by complex Cauchy-Schwarz. The quantified family includes the zero functional and every unnormalised mass phi(1). No faithfulness, normalisation or positive-mass premise is imposed.")),
            Paragraph(Text("For the quantitative statement set u=(2sqrt(2)/3,-1/3,0), e=(1/3,2sqrt(2)/3,0), f=(0,0,1), theta(rho)=8rho/3, D(rho)=(2+12rho squared)/9, E(rho)=(2+4rho squared)/9, A(rho)=3sqrt(D(rho)+theta(rho) squared*E(rho)), Lambda(rho)=sqrt(2)(1+64rho squared/9), M(rho)=3(sqrt(3)+3/2+2abs(rho))(1+theta(rho) squared), delta(rho)=Lambda(rho)-A(rho), and epsilon(rho)=delta(rho)/(2M(rho)). In the formulas below these are respectively dd, ee, amp, lam, bigM, delta and epsilon. Define eta(sigma,rho)=i*sigma*e+theta(rho)*f and xi(sigma,rho,q)=u+q*eta(sigma,rho). The positive functional vectorPhi(v) is the actual map a to star(v) dot (a*v).")),
            Describe.Lean(DescribeId.Create("exact-finite-violation"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/BalancedStarRigidity.exact_finite_witness"),
                H("The explicit finite violation at every nonzero residual"),
                StatementSource.FromAuthor(F.Disp(FiniteStatement())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The same phi=vectorPhi(xi(sigma,rho,epsilon(rho))) occurs in the mass, the L reading and both Gram budgets. The six frame identities assert that u,e,f are orthonormal in the standard complex inner product. The finite displacement epsilon is strictly positive for every nonzero rho, for either orientation.")),
                    Paragraph(Text("The proof evaluates the complete matrices at xi(sigma,rho,q), for every real q. The L reading equals -q*Lambda. With b=(9216rho to the fourth+8496rho squared+648)/1296, d=sqrt(2)(24576rho to the fourth+24192rho squared+2916)/1296 and Q=(164096rho to the fourth+69732rho squared+6561)/1296, the two actual Gram budgets are q squared*(b+q*d+q squared*Q) and q squared*(b-q*d+q squared*Q). Their sum is bounded by q*A+q squared*M for q>=0. This keeps every finite remainder, including all environment contributions.")),
                    Paragraph(Text("The scalar identities A squared=4b and Lambda squared-A squared=20rho squared/9+5888rho to the fourth/81 give delta>0 for rho nonzero. The estimate 4Q<=M squared and the nonnegativity of the actual Gram budgets control the two square roots. Substitution of q=delta/(2M) gives precisely the positive gap delta squared/(4M). No limiting response, supplied Gram identity or additional matrix premise is used."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("zero-probe-forces-zero"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/BalancedStarRigidity.zero_probe_forces_zero"),
                H("The zero-probe budget alone forces rho to vanish"),
                StatementSource.FromAuthor(F.Disp(ForParameters(Imp(ZeroBudget(),Eq(V("rho"),N(0)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If rho were nonzero, the explicit positive vector functional in the preceding theorem would violate the assumed zero-probe budget by a strictly positive amount. This implication has no P2 premise."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("full-equivalence"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/BalancedStarRigidity.full_equivalence"),
                H("All probes and the single zero probe have exactly the same rigidity"),
                StatementSource.FromAuthor(F.Disp(ForParameters(And(Iff(Eq(V("rho"),N(0)),AllBudgets()),Iff(AllBudgets(),ZeroBudget()))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("At rho=0, complex Cauchy-Schwarz gives read(phi,K(sigma,a,b)) squared<=B(phi,a,b) for every positive complex-linear phi and selfadjoint a,b. The standard multiplication identity gives K(sigma,Rplus,Splus)-K(sigma,Rminus,Sminus)=L. Applying the same phi, the triangle inequality and the two square-root bounds yields PB at every selfadjoint PAP probe. The fixed pair c,t also gives P2. All degeneracies and zero mass are included.")),
                    Paragraph(Text("This is a statement about the displayed fixed output in the given matrix algebra. It constructs no unknown total response, physical preparation, event menu or physical dynamics. The separate assertion that P2 alone admits rho=1/2 is not included. General inputs, infinite spectra, uniform approximation rates and full original physical-source reconstruction require their separate hypotheses and conclusions."))),
                DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula N(byte n) => F.D(n);
    private static Formula C(string s, params Formula[] xs) => new Formula.Apply(V(s),[..xs]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(s),t,b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Or,b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a,b);
    private static Formula Sq(Formula a) => C("pow",a,N(2));
    private static Formula Conj(params Formula[] xs) => xs.Aggregate(And);
    private static Formula Rl => F.Seq(F.Mathbb,F.Grp(V("R")));
    private static Formula Pos => C("PositiveFunctionals",V("A"));
    private static Formula G => C("g",V("sigma"),V("rho"));
    private static Formula Label(string name, Formula x) => name is "Rp" or "Rm" ? C(name,V("sigma"),x) : C(name,V("sigma"),V("rho"),x);
    private static Formula Reading(Formula phi, Formula a) => C("read",phi,a);
    private static Formula Gram(Formula phi, Formula a, Formula b) => C("B",phi,a,b);
    private static Formula Budget(Formula x, Formula phi) => Le(C("abs",Reading(phi,Label("L",x))),Add(C("sqrt",Gram(phi,Label("Rp",x),Label("Sp",x))),C("sqrt",Gram(phi,Label("Rm",x),Label("Sm",x)))));
    private static Formula ZeroBudget() => All("phi",Pos,Budget(N(0),V("phi")));
    private static Formula AllBudgets() => And(All("phi",Pos,Le(Sq(Reading(V("phi"),G)),Gram(V("phi"),V("c"),V("t")))),All("x",V("A"),Imp(C("CornerSA",V("x")),All("phi",Pos,Budget(V("x"),V("phi"))))));
    private static Formula ForParameters(Formula body) => All("sigma",Rl,All("rho",Rl,Imp(Or(Eq(V("sigma"),N(1)),Eq(V("sigma"),new Formula.Negate(N(1)))),body)));
    private static Formula Scalar(string name) => C(name,V("rho"));
    private static Formula FiniteStatement()
    {
        var eps=Scalar("epsilon"); var delta=Scalar("delta"); var mass=Add(N(1),Mul(Sq(eps),Add(N(1),Sq(Scalar("theta")))));
        var phi=C("vectorPhi",C("xi",V("sigma"),V("rho"),eps));
        var gap=Div(Sq(delta),Mul(N(4),Scalar("bigM")));
        Formula Inner(string a,string b) => C("dot",C("star",V(a)),V(b));
        var frame=Conj(Eq(Inner("u","u"),N(1)),Eq(Inner("e","e"),N(1)),Eq(Inner("f","f"),N(1)),Eq(Inner("u","e"),N(0)),Eq(Inner("u","f"),N(0)),Eq(Inner("e","f"),N(0)));
        var violation=Sub(Sub(C("abs",Reading(phi,Label("L",N(0)))),C("sqrt",Gram(phi,Label("Rp",N(0)),Label("Sp",N(0))))),C("sqrt",Gram(phi,Label("Rm",N(0)),Label("Sm",N(0)))));
        return ForParameters(Imp(new Formula.Relation(V("rho"),FormulaRelationOperator.NotEqual,N(0)),Conj(frame,Lt(N(0),delta),Lt(N(0),eps),Eq(C("apply",phi,N(1)),C("ofReal",mass)),Lt(N(0),gap),Le(gap,violation))));
    }
}
