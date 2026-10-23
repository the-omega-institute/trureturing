using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
#pragma warning disable IDE0051 // Shared DSL helper vocabulary intentionally exceeds each document formula set.
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;
internal sealed class CoordinateEdgeHamiltonianDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/CoordinateEdgeHamiltonian.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real conference coefficients realize normalized quadratic coordinate interactions.", H("Real quadratic edge interactions"), Blocks(
            Paragraph(Text("Natural subtraction is truncated at zero. All other divisions are in Real or Complex. Scalar casts retain their target type. Matrix products are operator products, and Matrix.conjTranspose is conjugate transpose. Subtype.val is the value of a density; Equiv.symm applied to CStarMatrix.ofMatrix recovers its ordinary matrix. Assignment N is the occupation basis Fin N → Bool. Implicit Lean mode and dimension arguments may be displayed explicitly. Bracketed Fintype, DecidableEq and Nonempty assumptions are anonymous instance arguments.")),
            Node("quadraticEdge","Real quadratic inter-site term",Quadratic(),"The real coefficient matrix multiplies the actual Jordan-Wigner Majorana matrices, with the factor i exactly as displayed.",DescribeRole.Definition),
            Node("averagedHamiltonian","Literal edge average",Average(),"The sum runs over all actual unordered edges and is multiplied by the reciprocal of their cardinality.",DescribeRole.Definition),
            Node("admissibleEdges","Interaction admissibility",Admissibility(),"Admissibility means Hermitian, operator norm at most one, and commutation with total occupation parity on each edge.",DescribeRole.Definition),
            Node("coordinateCoupling","Conference edge coefficients",Coupling(),"The coefficient is diagonal in the local Majorana index and uses the single coordinate in which the edge endpoints differ.",DescribeRole.Definition),
            Node("coordinate_edges_admissible","Admissible interactions on the coordinate graph",AdmissibleCoordinate(),"Every actual coordinate edge has one signed coefficient, giving a Hermitian involution with operator norm one and even total parity.",DescribeRole.Theorem))));
    private static DocumentBlock Node(string name,string title,Formula formula,string prose,DescribeRole role) =>
        Describe.Lean(DescribeId.Create("fgauss-coordinateedgehamiltonian-"+name.Replace("_","-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix+name),H(title),StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(prose))),role);

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

    private static Formula Quadratic()
    {
        var n=N("n");var m=N("m");var v=N("v");var w=N("w");var k=N("K");var p=N("p");var t=N("t");
        return EveryNM(All("v",F(n),All("w",F(n),All("K",C("Matrix",Local(m),Local(m),N("Real")),
            Eq(C("quadraticEdge",v,w,k),C("ofMatrix",Smul(Qualified("Complex.I"),SumAt("p",Local(m),SumAt("t",Local(m),
                Smul(C("asComplex",At(k,p,t)),Mul(Gamma(n,m,v,p),Gamma(n,m,w,t))))))))))));
    }
    private static Formula Average()
    {
        var n=N("n");var m=N("m");var g=N("G");var k=N("K");var z=N("z");var o=C("out",z);
        return EveryNM(All("G",Graph(n),All("K",Couplings(g,m),Eq(Avg(g,k),Smul(C("inv",C("asReal",C("edgeCard",g))),
            SumAt("z",Edge(g),C("quadraticEdge",C("fst",o),C("snd",o),At(k,z))))))));
    }
    private static Formula EdgeCondition(Formula n,Formula m,Formula g,Formula k)
    {
        var z=N("z");var o=C("out",z);var h=C("quadraticEdge",C("fst",o),C("snd",o),At(k,z));
        return All("z",Edge(g),And(C("IsSelfAdjoint",h),Le(new Formula.Norm(h),D(1)),C("Commute",h,C("ofMatrix",Pi(Mul(n,m))))));
    }
    private static Formula Admissibility()
    {
        var n=N("n");var m=N("m");var g=N("G");var k=N("K");
        return EveryNM(All("G",Graph(n),All("K",Couplings(g,m),Iff(C("admissibleEdges",g,k),EdgeCondition(n,m,g,k)))));
    }
    private static Formula Params(Formula b)
    {
        var n=N("n");var m=N("m");var q=N("q");var r=N("r");
        return EveryNM(All("q",N("Nat"),All("r",N("Nat"),All("e",C("Equiv",F(n),Fun(F(q),C("Index",r))),All("a",C("Equiv",F(q),Local(m)),b)))));
    }
    private static Formula CG() => C("coordinateComap",N("q"),N("r"),N("e"));
    private static Formula KC(Formula z) => C("coordinateCoupling",N("r"),N("e"),N("a"),z);
    private static Formula Coupling()
    {
        var z=N("z");var p=N("p");var u=N("u");var b=N("b");var a=N("a");var e=N("e");var t=C("equivInverse",a,p);
        var v=C("fst",C("out",z));var w=C("snd",C("out",z));var ev=At(e,v);var ew=At(e,w);
        var cond=And(Eq(p,u),All("b",F(N("q")),Imp(Ne(b,t),Eq(At(ev,b),At(ew,b)))));
        return Params(All("z",Edge(CG()),All("p",Local(N("m")),All("u",Local(N("m")),
            Eq(At(KC(z),p,u),C("ite",cond,C("asReal",At(C("conference",N("r")),At(ev,t),At(ew,t))),D(0)))))));
    }
    private static Formula AdmissibleCoordinate()
    {
        var z=N("z");var t=N("t");var e=N("e");var at=At(N("a"),t);var ev=At(e,C("fst",C("out",z)));var ew=At(e,C("snd",C("out",z)));
        return Params(And(C("admissibleEdges",CG(),C("coordinateCouplingFamily",N("r"),e,N("a"))),
            All("z",Edge(CG()),Ex("t",F(N("q")),And(Ne(At(ev,t),At(ew,t)),Eq(KC(z),C("matrixSingle",at,at,
                C("asReal",At(C("conference",N("r")),At(ev,t),At(ew,t))))))))));
    }

}
