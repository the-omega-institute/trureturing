using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Hopfield;

internal sealed class GayrardMixedMemoryRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Hopfield/GayrardMixedMemoryRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/StatisticalMechanics/gayrard2025mixedmemories");
    private static readonly Formula Nat = NumberSet("N"), Real = NumberSet("R");
    private static readonly Formula n = F.Id("n"), c = F.Id("c"), k = F.Id("k"), a = F.Id("a"),
        f = F.Id("F"), m = F.Id("m"), mu = F.Id("mu"), r = F.Id("r"),
        omega = F.Id("omega"), Omega = F.Id("Omega"), p = F.Id("P"),
        xi = F.Id("xi"), size = F.Id("M"), N = F.Id("N"), i = F.Id("i"), V = F.Id("V");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An asymmetric five-pattern mixed memory for quadratic activation lies outside the composition hierarchy. Exact correlations on the five-dimensional cube and the strong law yield its limiting overlaps.",
        H("The mixed-memory hierarchy is not complete"),
        Blocks(
            Node("allowable", "Allowable compositions", AllowableFormula(),
                AllowableProse(), "allowable"),
            Node("gamma", "Products along a composition", GammaFormula(),
                "For every positive block size a, PrecessionSpinOneSeparableBound.c(a) is the source's α^(a) = 2^(-a+1) binom(a-1,floor((a-1)/2)), reused from D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound; the source's (1.2.1.5), printed (1.10), p. 5, defines gamma(k) as the product of these factors in the first k blocks. Fin indices begin at zero, so gamma(c,k) takes k.val+1 blocks.", "gamma"),
            Node("system", "The strict hierarchy inequalities", SystemFormula(),
                "The source's system S, (1.2.1.12bis), printed (1.13), p. 5: for each nonfinal block, twice the derivative at its gamma value exceeds the sum of all later block lengths times the derivatives at their gamma values. The last block imposes no inequality.", "hierarchySystem"),
            Node("block", "The padded block vector", BlockFormula(),
                BlockProse(), "blockVector"),
            Node("coefficients", "The literal coefficient set", CoefficientFormula(),
                "The source's (1.2.1.15), printed (1.15), p. 6, takes all allowable compositions satisfying S, all permutations of the M coordinates, and all coordinate signs. The sign exponent is 1 if the derivative is odd and 2 otherwise. Here coefficientSet(n,F,M) is a Set of functions Fin(M) → R.", "coefficientSet"),
            Node("spin", "The mixed configuration", SpinFormula(),
                "Definition 1.1, p. 4, defines xi_i(m) = sign(sum_mu xi_i^mu F'(m_mu) 1_{m_mu ≠ 0}). The pattern and site indices are shifted by one: Lean mu and i correspond to source mu+1 and i+1. The source's sign convention (2.2.2), printed (2.25), p. 15, is +1 above zero, -1 below zero, and 0 at zero; Real.sign has precisely this convention. M(N) permits the number of patterns to vary with N.", "memorySpin"),
            Node("memory", "Mixed memories of type F", MemoryFormula(),
                MemoryProse(), "mixedMemory"),
            Node("claim", "Gayrard's Conjecture 1.4", ClaimFormula(),
                ClaimProse(), "claim"),
            Describe.Lean(DescribeId.Create("gayrard-result"), DeclarationHandle.Create(Prefix + "result"),
                H("An asymmetric five-pattern counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For F(x)=x²/2 and M(N)=5, take m=(5/8,3/8,3/8,1/8,1/8), padded by zeros. The integer fields 5x₁+3x₂+3x₃+x₄+x₅ never vanish. Summing each coordinate times their sign over all 32 cube points gives (20,12,12,4,4). An infinite product of fair Boolean coordinates supplies the independent patterns; the strong law yields the five normalized overlap limits. There are no unused coordinates among the first five. The allowable compositions of five are (5), (2,3), (4,1), (2,2,1), and every padded block coordinate has absolute value at most 1/2. Permutations and the prescribed sign powers preserve this bound, while m₁=5/8. Theorem 1.2's sufficient direction is compatible with this failure of necessity. No local-minimum assertion is made."))),
                DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose, string declaration) =>
        Node(id, title, formula, Paragraph(Text(prose)), declaration);
    private static DocumentBlock Node(string id, string title, Formula formula, DocumentBlock prose, string declaration) =>
        Describe.Lean(DescribeId.Create("gayrard-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromLiterature(Source),
            Blocks(prose), DescribeRole.Definition);
    private static Formula At(Formula value, Formula index) => new Formula.Subscript(value,index);
    private static Formula SourceConfiguration() => Seq(Pow(F.Xi,Parenthesized(N)),Parenthesized(m));
    private static DocumentBlock AllowableProse() => Paragraph(
        Text("Printed p. 5: \"We call an "), Math(F.Ell), Text("-composition ("),
        Math(At(n,D(1))), Text(",…,"), Math(At(n,F.Ell)), Text(") allowable if "),
        Math(Rel(At(n,k),FormulaRelationOperator.GreaterThanOrEqual,D(2))), Text(" is even for all "),
        Math(Seq(D(1),Sp,Leq,Sp,k,Sp,Leq,Sp,Sub(F.Ell,D(1)))), Text(" and "),
        Math(Rel(At(n,F.Ell),FormulaRelationOperator.GreaterThanOrEqual,D(1))), Text(" is odd.\" Mathlib Composition(n) is a list of strictly positive natural blocks summing to n. dropLast removes the last block; getLastD selects it, using zero only for an empty list. Nonemptiness excludes the empty composition. Indices are zero-based."));
    private static DocumentBlock BlockProse()
    {
        Formula g = At(GammaLower,n), srcMu = F.Mu;
        Formula mg = Seq(m,Parenthesized(g));
        Formula indices = Seq(D(1),Sp,Leq,Sp,srcMu,Sp,Leq,Sp,size);
        return Paragraph(Text("Printed p. 5: \"Given "),
            Math(Mem(g,At(Seq(Mathcal,Grp(F.Id("G"))),Seq(n,Comma,f)))),
            Text(", let "), Math(Eq(mg,At(Parenthesized(Seq(At(m,srcMu),Parenthesized(g))),indices))),
            Text(" be the vector whose components are constant and equal to "),
            Math(Pow(GammaLower,Parenthesized(k))), Text(" on consecutive blocks of length "),
            Math(At(n,k)), Text(", "), Math(Seq(D(1),Sp,Leq,Sp,k,Sp,Leq,Sp,F.Ell)),
            Text(", and are "), Math(D(0)), Text(" beyond,\" as displayed in (1.2.1.8), printed (1.14). Composition.index selects the unique block containing the zero-based coordinate mu; the dependent Fin constructor contains its bound proof h."));
    }
    private static DocumentBlock MemoryProse()
    {
        Formula srcMu = F.Mu, nu = F.Nu, muNu = At(srcMu,nu);
        Formula hatm = At(Seq(Widehat,Grp(m)),nu);
        Formula configs = At(Seq(Mathcal,Grp(F.Id("S"))),N);
        Formula sourceSpin = At(F.Xi,i);
        return Paragraph(
            Text("Definition 1.1, p. 4: \"Let "), Math(f),
            Text(" be a smooth function whose derivative satisfies "),
            Math(Seq(f,Apos,Parenthesized(F.Id("x")),Gt,D(0))),
            Text(", for all "), Math(Rel(F.Id("x"),FormulaRelationOperator.GreaterThan,D(0))), Text(". Given "), Math(Mem(n,Nat)),
            Text(" independent of "), Math(N), Text(", "), Math(n),
            Text("-mixed memories of type "), Math(f), Text(" are configurations in "), Math(configs),
            Text(" denoted by "), Math(Eq(SourceConfiguration(),At(Parenthesized(Seq(sourceSpin,Parenthesized(m))),Seq(D(1),Sp,Leq,Sp,i,Sp,Leq,Sp,N)))),
            Text(" and defined as\" the displayed spin formula. \"(i) "), Math(m),
            Text(" has exactly "), Math(n), Text(" non-zero components, i.e. there exists a subset "),
            Math(V), Text("⊂{1,…,M} of cardinality "), Math(Eq(Seq(Bar,V,Bar),n)),
            Text(" such that "), Math(Rel(At(m,srcMu),FormulaRelationOperator.NotEqual,D(0))),
            Text(" if and only if "), Math(Mem(srcMu,V)),
            Text(".\" \"Let {μ₁,…,μₙ} be an enumeration of the elements of "), Math(V),
            Text(" and, for each "), Math(Seq(D(1),Sp,Leq,Sp,nu,Sp,Leq,Sp,n)), Text(", set "),
            Math(Eq(At(m,muNu),hatm)), Text(". Then, for each "), Math(Seq(D(1),Sp,Leq,Sp,nu,Sp,Leq,Sp,n)),
            Text(", the normalised overlap of "), Math(SourceConfiguration()),
            Text(" with the pattern "), Math(Pow(F.Xi,muNu)), Text(" converges to "), Math(hatm),
            Text(" as "), Math(N), Text(" diverges,\" and \"and it converges to zero else,\" with probability one in (1.2.1.2) and (1.2.1.3). The formula records that configurations are binary almost surely. Each occupied coordinate converges to its coefficient; every coordinate appearing at some size and outside V converges to zero. The support V is independent of N. The hypotheses on F, n, M and the coordinate bounds are bound in claim."));
    }
    private static DocumentBlock ClaimProse() => Paragraph(
        Text("Conjecture 1.4, printed p. 6: \"Given any "), Math(Mem(n,Nat)),
        Text(" odd, "), Math(Seq(Pow(F.Xi,Parenthesized(N)),Parenthesized(m))),
        Text(" is an "), Math(n), Text("-mixed memory of type "), Math(f),
        Text(" if and only if "), Math(Mem(m,new Formula.Subscript(Seq(Mathcal,Grp(F.Id("M"))),Seq(n,Comma,f)))),
        Text(".\" The standing sentence on p. 4 is: \"Throughout the paper, "), Math(Mem(n,Nat)),
        Text(" is chosen to be independent of "), Math(N), Text(" and "), Math(size),
        Text(" is chosen to be a non-decreasing function of "), Math(N),
        Text(".\" An infinite deterministic sequence m represents coherent restrictions to the first M(N) coordinates. Membership is checked on each restriction. The probability space and jointly independent measurable family xi are arbitrary; both signs have mass 1/2. F is smooth with positive derivative on the positive half-line, n is odd, M is monotone, and every coefficient lies in [-1,1]. The two bracketed Lean instance arguments are anonymous."));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Qualified(string owner, string name) => Seq(F.Id(owner), Dot, F.Id(name));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Dotted(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula DotCall(string owner, string name, params Formula[] args) => new Formula.Apply(Dotted(owner, name), [.. args]);
    private static Formula App(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula Field(Formula value, string name) => Seq(value, Dot, Named(name));
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) => new Formula.Relation(left, op, right);
    private static Formula Eq(Formula left, Formula right) => Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula Lt(Formula left, Formula right) => Rel(left, FormulaRelationOperator.LessThan, right);
    private static Formula Le(Formula left, Formula right) => Rel(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) => new Formula.Logic(Parenthesized(left), op, Parenthesized(right));
    private static Formula And(params Formula[] values) => values.Aggregate((x,y) => Logic(x,FormulaLogicOperator.And,y));
    private static Formula Or(Formula x, Formula y) => Logic(x,FormulaLogicOperator.Or,y);
    private static Formula Imp(Formula x, Formula y) => Logic(x,FormulaLogicOperator.Implies,y);
    private static Formula Iff(Formula x, Formula y) => Logic(x,FormulaLogicOperator.Iff,y);
    private static Formula All(Formula variable, Formula type, Formula body) => Seq(Forall,Sp,variable,Sp,Colon,Sp,type,Comma,Sp,body);
    private static Formula Ex(Formula variable, Formula type, Formula body) => Seq(Exists,Sp,variable,Sp,Colon,Sp,type,Comma,Sp,body);
    private static Formula Arrow(Formula from, Formula to) => Seq(Parenthesized(from),Sp,To,Sp,Parenthesized(to));
    private static Formula NumberSet(string name) => Seq(Mathbb,Grp(F.Id(name)));
    private static Formula Fin(Formula bound) => Call("Fin",bound);
    private static Formula Val(Formula value) => Call("val",value);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value,Colon,type));
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Add,y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Subtract,y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Multiply,y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x,y);
    private static Formula Negate(Formula x) => new Formula.Negate(x);
    private static Formula Mem(Formula x, Formula set) => Seq(x,Sp,InMacro,Sp,set);
    private static Formula Not(Formula x) => new Formula.Not(x);
    private static Formula If(Formula cond, Formula yes, Formula no) => Seq(Named("if"),Sp,Parenthesized(cond),Sp,Named("then"),Sp,yes,Sp,Named("else"),Sp,no);
    private static Formula Lambda(Formula variable, Formula type, Formula body) => Parenthesized(Seq(variable,Colon,type,Sp,Mapsto,Sp,body));
    private static Formula Sum(Formula variable, Formula type, Formula body) => Seq(F.Sum,Underscore,Grp(variable,Colon,type),Sp,body);
    private static Formula SumIn(Formula variable, Formula set, Formula body) => Seq(F.Sum,Underscore,Grp(variable,Sp,InMacro,Sp,set),Sp,body);
    private static Formula AE(Formula variable, Formula measure, Formula body) =>
        DotCall("Filter","Eventually",Lambda(variable,Omega,body),Call("ae",measure));
    private static Formula WithInstance(Formula type, Formula body) => Seq(OpenBracket,type,CloseBracket,Sp,body);
    private static Formula Range(Formula bound) => DotCall("Finset","range",bound);
    private static Formula Gam(Formula comp, Formula idx) => Call("gamma",comp,idx);
    private static Formula Der(Formula fun, Formula x) => Call("deriv",fun,x);
    private static Formula Size(Formula comp) => Field(comp,"length");
    private static Formula CompType() => Call("Composition",n);
    private static Formula Patterns() => Arrow(Nat,Arrow(Nat,Arrow(Omega,Real)));
    private static Formula Spin(Formula site) => Call("memorySpin",f,size,m,xi,N,site,omega);
    private static Formula Limit(Formula target) => Call("Tendsto",
        Lambda(N,Nat,Mul(Pow(Cast(N,Real),Negate(D(1))),
            SumIn(i,Range(N),Mul(App(xi,mu,i,omega),Spin(i))))),
        Named("atTop"),Call("nhds",target));

    private static Formula AllowableFormula()
    {
        Formula even = All(a,Nat,Imp(Mem(a,DotCall("List","dropLast",Field(c,"blocks"))),And(Le(D(2),a),Call("Even",a))));
        Formula last = DotCall("List","getLastD",Field(c,"blocks"),D(0));
        return Disp(All(n,Nat,All(c,CompType(),Iff(Call("allowable",c),And(Not(Eq(Field(c,"blocks"),Seq(OpenBracket,CloseBracket))),even,Call("Odd",last))))));
    }
    private static Formula GammaFormula() => Disp(All(n,Nat,All(c,CompType(),All(k,Fin(Size(c)),Eq(Gam(c,k),
        DotCall("List","prod",DotCall("List","map",Qualified("PrecessionSpinOneSeparableBound", "c"),DotCall("List","take",Add(Val(k),D(1)),Field(c,"blocks")))))))));
    private static Formula SystemFormula()
    {
        Formula term = If(Lt(k,r),Mul(Cast(App(Field(c,"blocksFun"),r),Real),Der(f,Gam(c,r))),D(0));
        return Disp(All(n,Nat,All(f,Arrow(Real,Real),All(c,CompType(),Iff(Call("hierarchySystem",f,c),
            All(k,Fin(Size(c)),Imp(Lt(Add(Val(k),D(1)),Size(c)),Rel(Mul(D(2),Der(f,Gam(c,k))),FormulaRelationOperator.GreaterThan,Sum(r,Fin(Size(c)),term)))))))));
    }
    private static Formula BlockFormula()
    {
        Formula h = F.Id("h");
        Formula body = Seq(Named("if"),Sp,h,Colon,Lt(mu,n),Sp,Named("then"),Sp,
            Gam(c,App(Field(c,"index"),DotCall("Fin","mk",mu,h))),Sp,Named("else"),Sp,D(0));
        return Disp(All(n,Nat,All(c,CompType(),All(mu,Nat,Eq(Call("blockVector",c,mu),body)))));
    }
    private static Formula CoefficientFormula()
    {
        Formula pi = F.Id("pi"), eps = F.Id("eps"), x = F.Id("x");
        Formula exponent = If(All(x,Real,Eq(Der(f,Negate(x)),Negate(Der(f,x)))),D(1),D(2));
        Formula signs = All(mu,Fin(size),Or(Eq(App(eps,mu),Negate(D(1))),Eq(App(eps,mu),D(1))));
        Formula coordinates = All(mu,Fin(size),Eq(App(m,mu),Mul(Pow(App(eps,mu),exponent),Call("blockVector",c,Val(App(pi,mu))))));
        Formula body = Ex(c,CompType(),And(Call("allowable",c),Call("hierarchySystem",f,c),
            Ex(pi,DotCall("Equiv","Perm",Fin(size)),Ex(eps,Arrow(Fin(size),Real),And(signs,coordinates)))));
        return Disp(All(n,Nat,All(f,Arrow(Real,Real),All(size,Nat,All(m,Arrow(Fin(size),Real),
            Iff(Mem(m,Call("coefficientSet",n,f,size)),body))))));
    }
    private static Formula SpinFormula()
    {
        Formula term = Mul(Mul(App(xi,mu,i,omega),Der(f,App(m,mu))),If(Not(Eq(App(m,mu),D(0))),D(1),D(0)));
        Formula body = Eq(Spin(i),DotCall("Real","sign",SumIn(mu,Range(App(size,N)),term)));
        return Disp(All(Omega,Named("Type"),All(f,Arrow(Real,Real),All(size,Arrow(Nat,Nat),All(m,Arrow(Nat,Real),
            All(xi,Patterns(),All(N,Nat,All(i,Nat,All(omega,Omega,body)))))))));
    }
    private static Formula MemoryFormula()
    {
        Formula binary = All(N,Nat,All(i,Nat,Imp(Lt(i,N),AE(omega,p,Or(Eq(Spin(i),Negate(D(1))),Eq(Spin(i),D(1)))))));
        Formula support = All(N,Nat,And(Seq(V,Sp,Subseteq,Sp,Range(App(size,N))),
            All(mu,Nat,Imp(Mem(mu,Range(App(size,N))),Iff(Not(Eq(App(m,mu),D(0))),Mem(mu,V))))));
        Formula on = All(mu,Nat,Imp(Mem(mu,V),AE(omega,p,Limit(App(m,mu)))));
        Formula off = All(mu,Nat,Imp(Ex(N,Nat,Lt(mu,App(size,N))),Imp(Not(Mem(mu,V)),AE(omega,p,Limit(D(0))))));
        Formula body = Iff(Call("mixedMemory",p,n,f,size,m,xi),And(binary,
            Ex(V,Call("Finset",Nat),And(Eq(Field(V,"card"),n),support,on,off))));
        return Disp(All(Omega,Named("Type"),WithInstance(Call("MeasurableSpace",Omega),
            All(p,Call("Measure",Omega),All(n,Nat,All(f,Arrow(Real,Real),All(size,Arrow(Nat,Nat),All(m,Arrow(Nat,Real),All(xi,Patterns(),body)))))))));
    }
    private static Formula ClaimFormula()
    {
        Formula x = F.Id("x"), pair = F.Id("pair");
        Formula measurable = All(mu,Nat,All(i,Nat,Call("Measurable",App(xi,mu,i))));
        Formula independent = Call("iIndepFun",Lambda(pair,Seq(Nat,Sp,Times,Sp,Nat),App(xi,Field(pair,"fst"),Field(pair,"snd"))),p);
        Formula masses = All(mu,Nat,All(i,Nat,And(
            Eq(App(p,Seq(OpenBrace,omega,Colon,Omega,Sp,Mid,Sp,Eq(App(xi,mu,i,omega),D(1)),CloseBrace)),new Formula.Fraction(D(1),D(2))),
            Eq(App(p,Seq(OpenBrace,omega,Colon,Omega,Sp,Mid,Sp,Eq(App(xi,mu,i,omega),Negate(D(1))),CloseBrace)),new Formula.Fraction(D(1),D(2))))));
        Formula smooth = Call("ContDiff",Real,Dotted("Top","top"),f);
        Formula positive = All(x,Real,Imp(Lt(D(0),x),Lt(D(0),Der(f,x))));
        Formula bounds = All(mu,Nat,And(Le(Negate(D(1)),App(m,mu)),Le(App(m,mu),D(1))));
        Formula restrictions = All(N,Nat,Mem(Lambda(mu,Fin(App(size,N)),App(m,Val(mu))),Call("coefficientSet",n,f,App(size,N))));
        Formula target = Iff(Call("mixedMemory",p,n,f,size,m,xi),restrictions);
        Formula coeffs = All(m,Arrow(Nat,Real),Imp(bounds,target));
        Formula dimensions = All(n,Nat,Imp(Call("Odd",n),All(size,Arrow(Nat,Nat),Imp(Call("Monotone",size),coeffs))));
        Formula functions = All(f,Arrow(Real,Real),Imp(smooth,Imp(positive,dimensions)));
        Formula patterns = All(xi,Patterns(),Imp(measurable,Imp(independent,Imp(masses,functions))));
        Formula spaces = All(Omega,Named("Type"),WithInstance(Call("MeasurableSpace",Omega),
            All(p,Call("Measure",Omega),WithInstance(Call("IsProbabilityMeasure",p),patterns))));
        return Disp(Iff(F.Id("claim"),spaces));
    }
}
