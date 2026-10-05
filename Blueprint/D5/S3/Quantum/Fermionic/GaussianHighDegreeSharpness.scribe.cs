using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
#pragma warning disable IDE0051 // Shared DSL helper vocabulary intentionally exceeds each document formula set.
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;
internal sealed class GaussianHighDegreeSharpnessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/GaussianHighDegreeSharpness.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fermionic high-degree energy and free-energy constants are sharp.", H("Sharpness of the high-degree fermionic bounds"), Blocks(
            Paragraph(Text("Nat, Real and Complex denote natural, real and complex numbers. Matrix products are operator products, smul is scalar multiplication, densityValue is the CStarMatrix value of a density, and densityMatrix is its underlying ordinary matrix; ofMatrix and matrixOf are the canonical CStarMatrix equivalence and its inverse. Fin is the finite index type, Prod(A,B) is the product type A × B, sqrt is the real square root Real.sqrt, Assignment(N) is Fin(N) → Bool, and numberParity(N) is exp(iπ times the number operator). siteMajorana(n,m,v,p) means majorana(finProdFinEquiv(v,fst(p)),snd(p)) on Assignment(nm). All divisions below are real or complex divisions, as indicated by asReal and asComplex; inv is the corresponding scalar inverse. edgeCard(G) means G.edgeFinset.card, and coordinateCouplingFamily(r,e,a) is the function z ↦ coordinateCoupling(r,e,a,z). energyGap is the product-energy infimum minus the physical-energy infimum. freeGap compares the actual Gibbs density with the tensor product of its actual one-site marginals. The Majoranas are the concrete Jordan-Wigner matrices, with m modes at each vertex.")),
            Node("claim","Quantified uniform sharpness",Eq(N("claim"),Sharpness()),"Section VI, printed page 26: “It remains open, however, whether the constants in the resulting high-degree energy and free-energy estimates are optimal, since their derivation also uses edge averaging, Cauchy–Schwarz, and only the operator-norm normalization of the interactions.” The displayed statement expresses uniform optimality: for every positive mode count and every degree cutoff, the energy bound is attained on a finite regular graph, and the free-energy gap exceeds every smaller prefactor at some finite positive inverse temperature.",DescribeRole.Definition),
            Node("result","The high-degree constants are sharp",N("claim"),"Choose a power-of-two conference order s with 2m(s−1) at least the prescribed cutoff and take the Cartesian product of 2m complete graphs on s vertices. Its normalized quadratic interactions have product energy zero and physical ground energy −sqrt(2m/D). The entropy budget of the Gibbs product is at most log of the Fock dimension; choosing a sufficiently large finite positive beta gives the strict free-gap inequality.",DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("negari-2610-01860-high-degree-constant-sharpness"),
                    ResolutionKind.Proved)))));
    private static DocumentBlock Node(string name,string title,Formula formula,string prose,DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("fgauss-gaussianhighdegreesharpness-"+name.Replace("_","-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix+name),H(title),StatementSource.FromAuthor(Disp(formula)),
            (name == "claim" ? AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumStates/negari2026gaussianapproximation")) : AssessedProvenance.FromRepo()),Blocks(Paragraph(Text(prose))),role,
            openProblemResolutionClaim: resolution);

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
    private static Formula Pair(Formula t, Formula u) => C("Prod",t,u);
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

    private static Formula Sharpness()
    {
        var m=N("m");var c=N("c");var d0=N("D0");var n=N("n");var d=N("D");var g=N("G");var k=N("K");var hh=N("hH");var beta=N("beta");var h=Avg(g,k);
        var bound=C("sqrt",Frac(C("asReal",Mul(D(2),m)),C("asReal",d)));
        var body=And(Le(D(1),n),Le(d0,d),Le(D(1),d),C("IsRegularOfDegree",g,d),C("admissibleEdges",g,k),Eq(C("energyGap",h),bound),Ex("beta",N("Real"),And(Lt(D(0),beta),Lt(Mul(c,bound),C("freeGap",h,hh,beta)))));
        return All("m",N("Nat"),Imp(Le(D(1),m),All("c",N("Real"),Imp(Lt(c,D(1)),All("D0",N("Nat"),Ex("n",N("Nat"),Ex("D",N("Nat"),Ex("G",Graph(n),Ex("K",Couplings(g,m),Ex("hH",C("IsSelfAdjoint",h),body))))))))));
    }

}
