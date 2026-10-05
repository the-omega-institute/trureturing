using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
#pragma warning disable IDE0051 // Shared DSL helper vocabulary intentionally exceeds each document formula set.
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;
internal sealed class GibbsProductGapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/GibbsProductGap.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Physical Gibbs marginals yield the entropy-budget lower bound on the free gap.", H("The Gibbs product entropy budget"), Blocks(
            Paragraph(Text("Nat, Real and Complex denote natural, real and complex numbers. Matrix products are operator products, smul is scalar multiplication, densityValue is the CStarMatrix value of a density, and densityMatrix is its underlying ordinary matrix; ofMatrix and matrixOf are the canonical CStarMatrix equivalence and its inverse. Fin is the finite index type, ProdType(A, B) denotes the product type A × B (Lean A × B), Assignment(N) is Fin(N) → Bool, and numberParity(N) is exp(iπ times the number operator). siteMajorana(n,m,v,p) means majorana(finProdFinEquiv(v,fst(p)),snd(p)) on Assignment(nm). All divisions below are real or complex divisions, as indicated by asReal and asComplex; inv is the corresponding scalar inverse. edgeCard(G) means G.edgeFinset.card, and coordinateCouplingFamily(r,e,a) is the function z ↦ coordinateCoupling(r,e,a,z). setOf(x ↦ P(x)) denotes the literal predicate-defined set of real energy values, and sInf denotes its infimum. Function expressions are written with the mapsto binder. thermalState(H,hH,beta) is exp(-beta H) divided by its trace, with the Hermitian proof hH. The product of marginals is built from the actual one-site partial traces. Natural numbers in dimension logarithms are cast to Real.")),
            Node("energyGap","Difference of literal energy infima",EnergyGapDefinition(),"Both sets contain the actual trace energies of density states with the displayed physicality predicates. The infimum over all physical densities is subtracted from the product infimum.",DescribeRole.Definition),
            Node("freeEnergy","Free energy in nats",FreeEnergyDefinition(),"The entropy is von Neumann entropy using the natural logarithm.",DescribeRole.Definition),
            Node("freeGap","Actual Gibbs-to-product free-energy difference",FreeGapDefinition(),"The comparison state is the tensor product of the actual one-site marginals of the Gibbs density.",DescribeRole.Definition),
            Node("gibbs_product_free_bound","Ground-sector entropy-budget bound",GibbsBound(),"The Gibbs density commutes with global parity, hence every actual site marginal commutes with its local parity. Their product has zero interaction energy. A trace-one ground projection bounds the partition function below by exp(-beta E), while the product entropy is bounded above by the logarithm of the Fock dimension.",DescribeRole.Theorem))));
    private static DocumentBlock Node(string name,string title,Formula formula,string prose,DescribeRole role) =>
        Describe.Lean(DescribeId.Create("fgauss-gibbsproductgap-"+name.Replace("_","-").ToLowerInvariant()),
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

    private static Formula LambdaAt(string v,Formula t,Formula b) => Seq(LambdaLower,Parenthesized(Seq(N(v),Colon,t)),Mapsto,Parenthesized(b));
    private static Formula EnergySet(Formula n,Formula m,Formula h,string pred)
    {
        var rho=N("rho");var x=N("x");
        return C("setOf",LambdaAt("x",N("Real"),Ex("rho",DS(Ass(Mul(n,m))),And(C(pred,rho),Eq(x,Energy(h,rho))))));
    }
    private static Formula EnergyGapDefinition()
    {
        var n=N("n");var m=N("m");var h=N("H");
        return EveryNM(All("H",C("CStarMatrix",Ass(Mul(n,m)),Ass(Mul(n,m)),N("Complex")),Eq(C("energyGap",h),
            Sub(C("sInf",EnergySet(n,m,h,"physicalProduct")),C("sInf",EnergySet(n,m,h,"physicalState"))))));
    }
    private static Formula FreeEnergyDefinition()
    {
        var n=N("n");var m=N("m");var h=N("H");var beta=N("beta");var rho=N("rho");
        return EveryNM(All("H",C("CStarMatrix",Ass(Mul(n,m)),Ass(Mul(n,m)),N("Complex")),All("beta",N("Real"),All("rho",DS(Ass(Mul(n,m))),
            Eq(C("freeEnergy",h,beta,rho),Sub(Energy(h,rho),Frac(Ent(rho),beta)))))));
    }
    private static Formula SigmaState(Formula n,Formula m,Formula rho) => C("siteProduct",n,m,LambdaAt("v",F(n),C("oneSiteMarginal",n,m,N("v"),rho)));
    private static Formula FreeGapDefinition()
    {
        var n=N("n");var m=N("m");var h=N("H");var hh=N("hH");var beta=N("beta");var rho=C("thermalState",h,hh,beta);
        return EveryNM(All("H",C("CStarMatrix",Ass(Mul(n,m)),Ass(Mul(n,m)),N("Complex")),All("hH",C("IsSelfAdjoint",h),All("beta",N("Real"),
            Eq(C("freeGap",h,hh,beta),Sub(C("freeEnergy",h,beta,SigmaState(n,m,rho)),C("freeEnergy",h,beta,rho)))))));
    }
    private static Formula GibbsBound()
    {
        var n=N("n");var m=N("m");var g=N("G");var k=N("K");var hh=N("hH");var ground=N("ground");var e=N("E");var beta=N("beta");var h=Avg(g,k);var rho=C("thermalState",h,hh,beta);
        var hyp=And(C("admissibleEdges",g,k),C("IsStarProjection",Op(ground)),Eq(Mul(C("matrixOf",h),Op(ground)),Smul(C("asComplex",e),Op(ground))),Lt(D(0),beta));
        var concl=And(C("physicalProduct",SigmaState(n,m,rho)),Le(Sub(Neg(e),Frac(C("log",C("asReal",C("card",Ass(Mul(n,m))))),beta)),C("freeGap",h,hh,beta)));
        return EveryNM(All("G",Graph(n),All("K",Couplings(g,m),All("hH",C("IsSelfAdjoint",h),All("ground",DS(Ass(Mul(n,m))),All("E",N("Real"),All("beta",N("Real"),Imp(hyp,concl))))))));
    }

}
