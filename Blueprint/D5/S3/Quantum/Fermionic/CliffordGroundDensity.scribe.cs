using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
#pragma warning disable IDE0051 // Shared DSL helper vocabulary intentionally exceeds each document formula set.
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;
internal sealed class CliffordGroundDensityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/CliffordGroundDensity.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Paired Clifford bilinears have a physical trace-one ground projector.", H("The physical Clifford ground sector"), Blocks(
            Paragraph(Text("Nat, Real and Complex denote natural, real and complex numbers. Matrix products are operator products, smul is scalar multiplication, densityValue is the CStarMatrix value of a density, and densityMatrix is its underlying ordinary matrix; ofMatrix and matrixOf are the canonical CStarMatrix equivalence and its inverse. Fin is the finite index type, ProdType(A, B) denotes the product type A × B (Lean A × B), Assignment(N) is Fin(N) → Bool, and numberParity(N) is exp(iπ times the number operator). siteMajorana(n,m,v,p) means majorana(finProdFinEquiv(v,fst(p)),snd(p)) on Assignment(nm). All divisions below are real or complex divisions, as indicated by asReal and asComplex; inv is the corresponding scalar inverse. edgeCard(G) means G.edgeFinset.card, and coordinateCouplingFamily(r,e,a) is the function z ↦ coordinateCoupling(r,e,a,z). SumType(kappa,kappa) is a disjoint sum with injections inl and inr. The paired quadratic operator Q(eta) is the sum over k of i eta(inl(k)) eta(inr(k)). Hermitian means equality to the conjugate transpose, IsStarProjection means Hermitian and idempotent, Commute(A,B) means AB=BA. The cardinality equation fixes the Fock dimension.")),
            Node("paired_clifford_ground","Trace-one ground projector and universal lower bound",PairedGround(),"Each bilinear is a Hermitian involution. A single Majorana reverses its own bilinear and preserves the others, giving a joint minus projection of trace one. Complementary plus projections bound the energy of every density.",DescribeRole.Theorem))));
    private static DocumentBlock Node(string name,string title,Formula formula,string prose,DescribeRole role) =>
        Describe.Lean(DescribeId.Create("fgauss-cliffordgrounddensity-"+name.Replace("_","-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix+name),H(title),StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(prose))),role);

    private static Formula N(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula C(string name, params Formula[] xs) => new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. xs]);
    private static Formula Parenthesized(Formula x) => Seq(Open,x,Close);
    private static Formula All(string v, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(v),t,b);
    private static Formula Ex(string v, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(v),t,b);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.Equal,y);
    private static Formula Ne(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.NotEqual,y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.LessThanOrEqual,y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.LessThan,y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Multiply,y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Add,y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Subtract,y);
    private static Formula Neg(Formula x) => new Formula.Negate(x);
    private static Formula And(params Formula[] xs) => xs.Aggregate((x,y) => new Formula.Logic(Parenthesized(x),FormulaLogicOperator.And,Parenthesized(y)));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Parenthesized(x),FormulaLogicOperator.Implies,Parenthesized(y));
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(Parenthesized(x),FormulaLogicOperator.Iff,Parenthesized(y));
    private static Formula Frac(Formula x, Formula y) => new Formula.Fraction(x,y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x,y);
    private static Formula At(Formula f, params Formula[] xs) => C("val",new[]{f}.Concat(xs).ToArray());
    private static Formula F(Formula n) => C("Fin",n);
    private static Formula M(Formula t) => C("Matrix",t,t,N("Complex"));
    private static Formula DS(Formula t) => C("DensityState",t);
    private static Formula Ass(Formula n) => C("Assignment",n);
    private static Formula Fun(Formula t, Formula u) => new Formula.TypeArrow(t,u);
    private static Formula Pair(Formula t, Formula u) => C("ProdType",t,u);
    private static Formula Prod(Formula x, Formula y) => C("pair",x,y);
    private static Formula SumAt(string v, Formula t, Formula b) => Seq(new Formula.Subscript(Sum,Seq(N(v),Colon,t)),Parenthesized(b));
    private static Formula ProdAt(string v, Formula t, Formula b) => Seq(new Formula.Subscript(FormulaDsl.Prod,Seq(N(v),Colon,t)),Parenthesized(b));
    private static Formula Inst(Formula t, Formula b, params string[] names) => Seq(names.SelectMany(name => new Formula[]{OpenBracket,C(name,t),CloseBracket,Sp}).Append(b).ToArray());
    private static Formula Smul(Formula s, Formula x) => C("smul",s,x);
    private static Formula One(Formula t) => Parenthesized(Seq(D(1),Colon,M(t)));
    private static Formula Pi(Formula n) => C("numberParity",n);
    private static Formula Gamma(Formula n,Formula m,Formula v,Formula p) => C("siteMajorana",n,m,v,p);
    private static Formula Local(Formula m) => Pair(F(m),N("Bool"));
    private static Formula Graph(Formula n) => C("SimpleGraph",F(n));
    private static Formula Edge(Formula g) => C("edgeSet",g);
    private static Formula Couplings(Formula g,Formula m) => Fun(Edge(g),C("Matrix",Local(m),Local(m),N("Real")));
    private static Formula Avg(Formula g,Formula k) => C("averagedHamiltonian",g,k);
    private static Formula Energy(Formula h,Formula rho) => C("meanEnergy",h,rho);
    private static Formula Op(Formula rho) => C("densityMatrix",rho);
    private static Formula Ent(Formula rho) => C("vonNeumannEntropy",rho);
    private static Formula EveryNM(Formula b) => All("n",N("Nat"),All("m",N("Nat"),b));
    private static Formula QuantumLabels(Formula m) => Local(m);

    private static Formula EtaQ(Formula eta,Formula kap) => SumAt("k",kap,Smul(N("imaginaryUnit"),Mul(At(eta,C("inl",N("k"))),At(eta,C("inr",N("k"))))));
    private static Formula CAR(Formula labels,Formula eta,Formula omega) => All("p",labels,All("t",labels,
        Eq(Add(Mul(At(eta,N("p")),At(eta,N("t"))),Mul(At(eta,N("t")),At(eta,N("p")))),C("ite",Eq(N("p"),N("t")),Smul(C("asComplex",D(2)),One(omega)),D(0)))));
    private static Formula PairedGround()
    {
        var kap=N("kappa");var omega=N("Omega");var eta=N("eta");var t=N("T");var p=N("p");var rho=N("rho");var w=N("omega");var labels=C("SumType",kap,kap);var q=EtaQ(eta,kap);
        var hyp=And(Eq(C("card",omega),Pow(D(2),C("card",kap))),All("p",labels,C("IsHermitian",At(eta,p))),CAR(labels,eta,omega),
            All("p",labels,Eq(Mul(t,At(eta,p)),Neg(Mul(At(eta,p),t)))));
        var concl=Ex("rho",DS(omega),And(C("IsStarProjection",Op(rho)),C("Commute",C("densityValue",rho),C("ofMatrix",t)),
            Eq(Mul(q,Op(rho)),Smul(Neg(C("asComplex",C("card",kap))),Op(rho))),
            All("omega",DS(omega),Le(Neg(C("asReal",C("card",kap))),Energy(C("ofMatrix",q),w)))));
        return All("kappa",N("Type"),All("Omega",N("Type"),Inst(kap,Inst(omega,
            All("eta",Fun(labels,M(omega)),All("T",M(omega),Imp(hyp,concl))),"Fintype","DecidableEq","Nonempty"),"Fintype","DecidableEq")));
    }

}
