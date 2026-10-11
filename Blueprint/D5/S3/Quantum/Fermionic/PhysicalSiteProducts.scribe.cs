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
            Paragraph(Text("Natural subtraction is truncated at zero. All other divisions are in Real or Complex. Scalar casts retain their target type. Matrix products are operator products, and Matrix.conjTranspose is conjugate transpose. Subtype.val is the value of a density; Equiv.symm applied to CStarMatrix.ofMatrix recovers its ordinary matrix. Assignment N is the occupation basis Fin N → Bool. Implicit Lean mode and dimension arguments may be displayed explicitly. Bracketed Fintype, DecidableEq and Nonempty assumptions are anonymous instance arguments.")),
            Node("siteProduct","Literal site tensor density",TensorProduct(),"The matrix entries are the product of the site density entries, with occupation configurations transported by the site equivalence. Positivity and trace one are part of the density type.",DescribeRole.Definition),
            Node("oneSiteMarginal","Actual one-site partial trace",Marginal(),"The density is reindexed by the split-site equivalence and its complementary-site factor is traced out.",DescribeRole.Definition),
            Node("physicalState","Global physicality",Physical(),"“Physical fermionic states obey the parity superselection rule” [printed page 3]: [ρ,P] = 0. Here P is the exponential of the number operator; rho.val is the actual density matrix.",DescribeRole.Definition),
            Node("physicalProduct","Physical site product",ProductPhysical(),"The witnesses are genuine site densities, each commuting with its local number parity. Their tensor density is the specified state.",DescribeRole.Definition),
            Node("siteParity","Local site parity on the Fock space",ParityDefinition(),"This diagonal operator records the occupation parity at the selected site.",DescribeRole.Definition),
            Node("one_site_marginal_physical","Physicality of every actual marginal",MarginalPhysical(),"Global parity factors through a selected site and its complement. Tracing over the complement cancels its nonzero parity signs and leaves local parity commutation.",DescribeRole.Theorem),
            Node("site_parity_majorana","Action of site parity on Majoranas",ParityMajorana(),"A Jordan-Wigner matrix changes precisely one occupation bit. The selected site parity therefore flips exactly the Majoranas at that site.",DescribeRole.Theorem),
            Node("physical_products_zero","Zero product energy",ProductZero(),"Conjugation by the parity of the first endpoint preserves a physical site product and reverses the interaction. Its trace against that product is zero, and the literal average has zero energy.",DescribeRole.Theorem))));
    private static DocumentBlock Node(string name,string title,Formula formula,string prose,DescribeRole role) =>
        Describe.Lean(DescribeId.Create("fgauss-physicalsiteproducts-"+name.Replace("_","-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix+name),H(title),StatementSource.FromAuthor(Disp(formula)),
            (name == "physicalState" ? AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumBounds/negari2026gaussianapproximation")) : AssessedProvenance.FromRepo()),Blocks(Paragraph(Text(prose))),role);

    private static Formula N(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula C(string name, params Formula[] xs) => name switch
    {

        "ProdType" or "PairType" => Qualified("Prod", xs),
        "SumType" => Qualified("Sum", xs),
        "pair" => Qualified("Prod.mk", xs),
        "fst" => Qualified("Prod.fst", xs),
        "snd" => Qualified("Prod.snd", xs),
        "asReal" => Cast(xs[0], "Real"),
        "asComplex" => Cast(xs[0], "Complex"),
        "asInt" => Cast(xs[0], "Int"),
        "card" => Qualified("Fintype.card", xs),
        "edgeCount" or "edgeCard" => Qualified("Finset.card", Qualified("SimpleGraph.edgeFinset", xs)),
        "edgeSet" => Qualified("SimpleGraph.edgeSet", xs),
        "IsRegularOfDegree" => Qualified("SimpleGraph.IsRegularOfDegree", xs),
        "out" => Qualified("Sym2.out", Qualified("Subtype.val", xs)),
        "densityValue" => Qualified("Subtype.val", xs),
        "densityMatrix" => new Formula.Apply(Qualified("Equiv.symm", Qualified("CStarMatrix.ofMatrix")), [Qualified("Subtype.val", xs)]),
        "matrixOf" => new Formula.Apply(Qualified("Equiv.symm", Qualified("CStarMatrix.ofMatrix")), [.. xs]),
        "ofMatrix" => Qualified("CStarMatrix.ofMatrix", xs),
        "IsHermitian" => Qualified("Matrix.IsHermitian", xs),
        "transpose" => Qualified("Matrix.transpose", xs),
        "diagonal" => Qualified("Matrix.diagonal", xs),
        "trace" => Qualified("Matrix.trace", xs),
        "matrixSingle" => Qualified("Matrix.single", xs),
        "sqrt" or "squareRoot" => Qualified("Real.sqrt", xs),
        "log" => Qualified("Real.log", xs),
        "exp" => Qualified("NormedSpace.exp", xs),
        "pi" => Qualified("Real.pi"),
        "ComplexI" => Qualified("Complex.I"),
        "smul" => Qualified("SMul.smul", xs),
        "inv" => Qualified("Inv.inv", xs),
        "neg" => new Formula.Negate(xs[0]),
        "Fun" => new Formula.TypeArrow(xs[0], xs[1]),
        "M" => Qualified("Matrix", xs[0], xs[0], new Formula.Symbol(FormulaIdentifier.Create("Complex"))),
        "realIdentity" => Parenthesized(Seq(D(1), Colon, Qualified("Matrix", xs[0], xs[0], new Formula.Symbol(FormulaIdentifier.Create("Real"))))),
        "zero" => Parenthesized(Seq(D(0), Colon, xs[0])),
        "inl" => Qualified("Sum.inl", xs),
        "inr" => Qualified("Sum.inr", xs),
        "fromBlocks" => Qualified("Matrix.fromBlocks", xs),
        "Matrix2x2" => Seq(Bang, Bang, OpenBracket, xs[0], Comma, xs[1], Semi, xs[2], Comma, xs[3], CloseBracket),
        "letInstance" => Seq(FormulaDsl.Id("letI"), Sp, Colon, FormulaDsl.Eq, Sp, xs[0], Semi, Sp, xs[1]),
        "coordinateCouplingFamily" => Qualified("coordinateCoupling", xs),
        "coordinateComap" => Qualified("SimpleGraph.comap", Qualified("coordinateGraph", xs[0], Qualified("Index", xs[1])), xs[2]),
        "equivInverse" => new Formula.Apply(Qualified("Equiv.symm", xs[0]), [xs[1]]),
        "inverseEquiv" => Qualified("Equiv.symm", xs),
        "siteMajorana" => Qualified("majorana", Mul(xs[0], xs[1]), Qualified("finProdFinEquiv", Qualified("Prod.mk", xs[2], Qualified("Prod.fst", xs[3]))), Qualified("Prod.snd", xs[3])),
        "siteOccupation" => LambdaTerm("j", F(xs[1]), At(xs[2], Qualified("finProdFinEquiv", Qualified("Prod.mk", xs[3], N("j"))))),
        "ComplementSites" => Qualified("Subtype", LambdaTerm("w", F(xs[0]), Ne(N("w"), xs[1]))),
        "splitSite" => Qualified("Equiv.trans", Qualified("Equiv.trans", Qualified("Equiv.arrowCongr", Qualified("Equiv.symm", Qualified("finProdFinEquiv")), Qualified("Equiv.refl", N("Bool"))), Qualified("Equiv.curry", F(xs[0]), F(xs[1]), N("Bool"))), Qualified("Equiv.funSplitAt", xs[2], Ass(xs[1]))),
        _ => new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. xs])
    };
    private static Formula Qualified(string name, params Formula[] arguments)
    {
        var parts = name.Split('.');
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count != 0) items.Add(Dot);
            items.Add(Operatorname);
            items.Add(Grp(FormulaDsl.Id(part)));
        }
        Formula function = Seq(items.ToArray());
        return arguments.Length == 0 ? function : new Formula.Apply(function, [.. arguments]);
    }
    private static Formula Cast(Formula value, string type) =>
        Parenthesized(Seq(value, Colon, new Formula.Symbol(FormulaIdentifier.Create(type))));
    private static Formula LambdaTerm(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Parenthesized(Seq(new Formula.Symbol(FormulaIdentifier.Create(name)), Colon, type)), Mapsto, Parenthesized(body));

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
