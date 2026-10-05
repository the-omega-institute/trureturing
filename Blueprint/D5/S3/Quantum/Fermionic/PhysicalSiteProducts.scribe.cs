using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
#pragma warning disable IDE0051 // Shared DSL helper vocabulary intentionally exceeds each document formula set.
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;
internal sealed class PhysicalSiteProductsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/PhysicalSiteProducts.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tensor site densities and their actual partial traces obey local number parity.", H("Physical tensor products and partial traces"), Blocks(
            Paragraph(Text("Nat, Real and Complex denote natural, real and complex numbers. Matrix products are operator products, smul is scalar multiplication, densityValue is the CStarMatrix value of a density, and densityMatrix is its underlying ordinary matrix; ofMatrix and matrixOf are the canonical CStarMatrix equivalence and its inverse. Fin is the finite index type, ProdType(A, B) denotes the product type A × B (Lean A × B), Assignment(N) is Fin(N) → Bool, and numberParity(N) is exp(iπ times the number operator). siteMajorana(n,m,v,p) means majorana(finProdFinEquiv(v,fst(p)),snd(p)) on Assignment(nm). All divisions below are real or complex divisions, as indicated by asReal and asComplex; inv is the corresponding scalar inverse. edgeCard(G) means G.edgeFinset.card, and coordinateCouplingFamily(r,e,a) is the function z ↦ coordinateCoupling(r,e,a,z). siteOccupation(n,m,x,v) is the function j ↦ x(finProdFinEquiv(v,j)). splitSite(n,m,v) is the composition of arrowCongr(finProdFinEquiv.symm,refl Bool), curry(Fin n,Fin m,Bool) and funSplitAt(v,Assignment m). ComplementSites(n,v) is the subtype of vertices different from v.")),
            Node("siteProduct","Literal site tensor density",TensorProduct(),"The matrix entries are the product of the site density entries, with occupation configurations transported by the site equivalence. Positivity and trace one are part of the density type.",DescribeRole.Definition),
            Node("oneSiteMarginal","Actual one-site partial trace",Marginal(),"The density is reindexed by the split-site equivalence and its complementary-site factor is traced out.",DescribeRole.Definition),
            Node("physicalState","Global physicality",Physical(),"A physical density commutes with total occupation parity.",DescribeRole.Definition),
            Node("physicalProduct","Physical site product",ProductPhysical(),"The witnesses are genuine site densities, each commuting with its local number parity. Their tensor density is the specified state.",DescribeRole.Definition),
            Node("siteParity","Local site parity on the Fock space",ParityDefinition(),"This diagonal operator records the occupation parity at the selected site.",DescribeRole.Definition),
            Node("one_site_marginal_physical","Physicality of every actual marginal",MarginalPhysical(),"Global parity factors through a selected site and its complement. Tracing over the complement cancels its nonzero parity signs and leaves local parity commutation.",DescribeRole.Theorem),
            Node("site_parity_majorana","Action of site parity on Majoranas",ParityMajorana(),"A Jordan-Wigner matrix changes precisely one occupation bit. The selected site parity therefore flips exactly the Majoranas at that site.",DescribeRole.Theorem),
            Node("physical_products_zero","Zero product energy",ProductZero(),"Conjugation by the parity of the first endpoint preserves a physical site product and reverses the interaction. Its trace against that product is zero, and the literal average has zero energy.",DescribeRole.Theorem))));
    private static DocumentBlock Node(string name,string title,Formula formula,string prose,DescribeRole role) =>
        Describe.Lean(DescribeId.Create("fgauss-physicalsiteproducts-"+name.Replace("_","-").ToLowerInvariant()),
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

    private static Formula SiteStates(Formula n,Formula m) => Fun(F(n),DS(Ass(m)));
    private static Formula TensorProduct()
    {
        var n=N("n");var m=N("m");var x=N("x");var y=N("y");var v=N("v");var states=N("states");
        return EveryNM(All("states",SiteStates(n,m),All("x",Ass(Mul(n,m)),All("y",Ass(Mul(n,m)),
            Eq(At(Op(C("siteProduct",n,m,states)),x,y),ProdAt("v",F(n),At(Op(At(states,v)),
                C("siteOccupation",n,m,x,v),C("siteOccupation",n,m,y,v))))))));
    }
    private static Formula Marginal()
    {
        var n=N("n");var m=N("m");var v=N("v");var rho=N("rho");var x=N("x");var y=N("y");var z=N("z");
        var inv=C("inverseEquiv",C("splitSite",n,m,v));
        return EveryNM(All("v",F(n),All("rho",DS(Ass(Mul(n,m))),All("x",Ass(m),All("y",Ass(m),
            Eq(At(Op(C("oneSiteMarginal",n,m,v,rho)),x,y),SumAt("z",Fun(C("ComplementSites",n,v),Ass(m)),
                At(Op(rho),At(inv,Prod(x,z)),At(inv,Prod(y,z))))))))));
    }
    private static Formula Physical()
    {
        var n=N("n");var m=N("m");var rho=N("rho");
        return EveryNM(All("rho",DS(Ass(Mul(n,m))),Iff(C("physicalState",rho),C("Commute",C("densityValue",rho),C("ofMatrix",Pi(Mul(n,m)))))));
    }
    private static Formula ProductPhysical()
    {
        var n=N("n");var m=N("m");var rho=N("rho");var states=N("states");var v=N("v");
        return EveryNM(All("rho",DS(Ass(Mul(n,m))),Iff(C("physicalProduct",rho),Ex("states",SiteStates(n,m),And(
            All("v",F(n),C("Commute",C("densityValue",At(states,v)),C("ofMatrix",Pi(m)))),Eq(rho,C("siteProduct",n,m,states)))))));
    }
    private static Formula ParityDefinition()
    {
        var n=N("n");var m=N("m");var v=N("v");var x=N("x");var y=N("y");
        return EveryNM(All("v",F(n),All("x",Ass(Mul(n,m)),All("y",Ass(Mul(n,m)),
            Eq(At(C("siteParity",n,m,v),x,y),C("ite",Eq(x,y),At(Pi(m),C("siteOccupation",n,m,x,v),C("siteOccupation",n,m,x,v)),D(0)))))));
    }
    private static Formula MarginalPhysical()
    {
        var n=N("n");var m=N("m");var v=N("v");var rho=N("rho");
        return EveryNM(All("v",F(n),All("rho",DS(Ass(Mul(n,m))),Imp(C("physicalState",rho),
            C("Commute",C("densityValue",C("oneSiteMarginal",n,m,v,rho)),C("ofMatrix",Pi(m)))))));
    }
    private static Formula ParityMajorana()
    {
        var n=N("n");var m=N("m");var v=N("v");var w=N("w");var j=N("j");var b=N("b");
        var p=C("siteParity",n,m,v);var gamma=Gamma(n,m,w,Prod(j,b));
        return EveryNM(All("v",F(n),All("w",F(n),All("j",F(m),All("b",N("Bool"),And(C("IsHermitian",p),
            Eq(Mul(p,p),One(Ass(Mul(n,m)))),Eq(Mul(p,gamma),Smul(C("ite",Eq(v,w),Neg(C("asComplex",D(1))),C("asComplex",D(1))),Mul(gamma,p)))))))));
    }
    private static Formula ProductZero()
    {
        var n=N("n");var m=N("m");var g=N("G");var k=N("K");var rho=N("rho");
        return EveryNM(All("G",Graph(n),All("K",Couplings(g,m),All("rho",DS(Ass(Mul(n,m))),
            Imp(C("physicalProduct",rho),Eq(Energy(Avg(g,k),rho),D(0)))))));
    }

}
