using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KarpZhangNinh;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/karpzhang2023pochhammer");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Triple rising-factorial series preserve coefficientwise log-concavity.",
        H("Karp and Zhang's Conjecture 3.8"), Blocks(
            KernelNode("a", "The positive-degree coefficient", DescribeRole.Definition, KernelAFormula(),
                "Conjecture 3.8, page 8: “Assume that {fₙ}ₙ₌₀∞ is log-concave and independent of µ. Then the function µ → f(µ; x) = ∑ₙ₌₁∞ fₙ (µ)₃ₙ/(3n − 1)! xⁿ is coefficient-wise log-concave.” The coefficient in positive degree is the displayed rising-factorial quotient. Its degree-zero extension is zero because the series starts at one.", true),
            KernelNode("raw", "The unpaired Turanian kernel", DescribeRole.Definition, KernelRawFormula(),
                "The two products are the degree-k and degree-(m-k) factors in the two Cauchy products. Natural subtraction is used only for indices in the finite coefficient sum."),
            KernelNode("paired", "The reflected kernel", DescribeRole.Definition, KernelPairedFormula(),
                "Reflection sends k to m-k. The central index contributes once, while every other paired term is the sum of both reflected terms."),
            KernelNode("pairPoch", "The factorial-free paired difference", DescribeRole.Definition, KernelPairFormula(),
                "Lemma 3.1, printed page 4: “Let k, m ∈ N₀ with k ≤ m/2, µ ≥ 0 and α, β > 0. Set”. Formula (8) defines Tₖ,ₘ as (µ+α)ₖ(µ+β)ₘ₋ₖ + (µ+α)ₘ₋ₖ(µ+β)ₖ − (µ)ₖ(µ+α+β)ₘ₋ₖ − (µ)ₘ₋ₖ(µ+α+β)ₖ. The displayed pairPoch uses a, b, c and N for µ, α, β and m. It is the paired kernel before positive factorial denominators are removed.", true),
            KernelNode("a_continuous", "Polynomial parameter dependence", DescribeRole.Theorem,
                KernelAll("n", KernelN(), KernelCall("Continuous", KernelCall("a", KernelX("n")))),
                "Every coefficient is a polynomial divided by a fixed positive factorial. Continuity supplies the boundary values of parameter inequalities."),
            KernelNode("paired_sign_step", "Strict backward propagation", DescribeRole.Theorem, KernelStepFormula(),
                "Lemma 3.1, printed page 4: “If Tₖ,ₘ ≤ 0 for some 1 ≤ k ≤ m/2, then Tₖ₋₁,ₘ < 0.” The source allows µ ≥ 0; the theorem uses its positive-µ specialization a > 0. Comparing the four reciprocal multipliers after moving one factor from the shorter length to the longer length proves the stated backward implication.", true),
            KernelNode("paired_sign", "At most one sign change", DescribeRole.Theorem, KernelSignFormula(),
                "Backward propagation between rising-factorial lengths 3i and 3j excludes a positive triple-Pochhammer pair followed by a negative one. Positive factorial denominators preserve signs; the middle pair has an additional positive factor of two."),
            Describe.Lean(DescribeId.Create("karp-zhang-ninh-delta"),
                DeclarationHandle.Create("D5/S3/Analytic/KarpZhangNinh/Result.delta"),
                H("The Turanian coefficient"), StatementSource.FromAuthor(DeltaFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The source defines the Turanian as f(mu+alpha;x)f(mu+beta;x)-f(mu;x)f(mu+alpha+beta;x). Its coefficientwise convention, printed page 1, is: “if the coefficients δₖ at all powers of x in (2) are non-negative (non-positive) for all α, β ≥ 0 we will say that µ → f(µ; x) is coefficient-wise log-concave (log-convex ).” Here Kernel.a has zero constant coefficient, so the endpoint summands vanish. A single coefficient sequence is fixed independently of all three real parameters."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("karp-zhang-ninh-convolution"),
                DeclarationHandle.Create("D5/S3/Analytic/KarpZhangNinh/Result.Z"),
                H("The unweighted convolution"), StatementSource.FromAuthor(ZFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Multiplication by (3m)! identifies this convolution with the beta lift of Homogeneous.P. Homogeneous balancing therefore passes to the rising-factorial convolution."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("karp-zhang-ninh-claim"),
                DeclarationHandle.Create("D5/S3/Analytic/KarpZhangNinh/Result.claim"),
                H("The exact coefficient assertion"), StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Conjecture 3.8, page 8: “Assume that {fₙ}ₙ₌₀∞ is log-concave and independent of µ. Then the function µ → f(µ; x) = Σₙ₌₁∞ fₙ (µ)₃ₙ/(3n − 1)! xⁿ is coefficient-wise log-concave.”")),
                    Paragraph(Text("The reused KarpZhangReciprocal.Result.IsLogConcave is Definition 1.1, including nonnegativity, nontriviality, adjacent inequalities and interval support. Every natural coefficient degree and all nonnegative real base parameters and shifts are quantified. The finite Cauchy sums require no analytic convergence assumption."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("karp-zhang-ninh-result"),
                DeclarationHandle.Create("D5/S3/Analytic/KarpZhangNinh/Result.result"),
                H("Nonnegativity in every degree"), StatementSource.FromAuthor(Disp(F.Id("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Trisection binomial identities prove homogeneous balancing. The general symmetric beta-lifting theorem transfers balancing to Z and makes its full Turanian sum nonnegative. The paired rising-factorial sign lemma and the existing KarpZhangGamma.Weighting.weighted_sum_nonneg give nonnegative central tails. The existing KarpZhangReciprocal.Result.abel_layers decomposes delta into these tails with increments of f(k)f(m-k); balanced_step makes every increment nonnegative. Polynomial continuity includes zero parameters and zero shifts."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("karp-zhang-2023-conjecture-3-8"),
                    ResolutionKind.Proved)))));

    private static Formula DeltaFormula()
    {
        Formula f = F.Id("f"), m = F.Id("m"), k = F.Id("k");
        Formula mu = F.Id("mu"), alpha = F.Id("alpha"), beta = F.Id("beta");
        Formula term = Multiply(Multiply(App(f,k), App(f,Subtract(m,k))),
            App(Q("Kernel","raw"),mu,alpha,beta,m,k));
        Formula sum = Seq(Sum,Underscore,Grp(k,Sp,InMacro,Sp,
            App(Q("Finset","range"),Add(m,Num(1)))),Sp,term);
        return Disp(All("f",new Formula.TypeArrow(F.Id("Nat"),F.Id("Real")),
            All("mu",F.Id("Real"),All("alpha",F.Id("Real"),All("beta",F.Id("Real"),
            All("m",F.Id("Nat"),Equal(App(F.Id("delta"),f,mu,alpha,beta,m),sum)))))));
    }

    private static Formula ZFormula()
    {
        Formula m = F.Id("m"), k = F.Id("k"), u = F.Id("u"), v = F.Id("v");
        Formula term = Multiply(App(Q("Kernel","a"),k,u), App(Q("Kernel","a"),Subtract(m,k),v));
        Formula sum = Seq(Sum,Underscore,Grp(k,Sp,InMacro,Sp,
            App(Q("Finset","range"),Add(m,Num(1)))),Sp,term);
        return Disp(All("m",F.Id("Nat"),All("u",F.Id("Real"),All("v",F.Id("Real"),
            Equal(App(F.Id("Z"),m,u,v),sum)))));
    }

    private static Formula ClaimFormula()
    {
        Formula f = F.Id("f"), mu = F.Id("mu"), alpha = F.Id("alpha"), beta = F.Id("beta");
        Formula assertion = All("f",new Formula.TypeArrow(F.Id("Nat"),F.Id("Real")),
            All("mu",F.Id("Real"),All("alpha",F.Id("Real"),All("beta",F.Id("Real"),
            All("m",F.Id("Nat"),Implies(App(Q("KarpZhangReciprocal","Result","IsLogConcave"),f),
                Implies(Le(Num(0),mu),Implies(Le(Num(0),alpha),Implies(Le(Num(0),beta),
                    Le(Num(0),App(F.Id("delta"),f,mu,alpha,beta,F.Id("m"))))))))))));
        return Disp(Iff(F.Id("claim"),assertion));
    }
    private static Formula All(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(n),t,b);
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f,[.. a]);
    private static Formula Q(string a,string b) => Seq(Operatorname,Grp(F.Id(a)),Dot,Operatorname,Grp(F.Id(b)));
    private static Formula Q(string a,string b,string c) => Seq(Q(a,b),Dot,Operatorname,Grp(F.Id(c)));
    private static Formula Le(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Implies(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Iff(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Iff,b);

    private static DocumentBlock KernelNode(string name, string title, DescribeRole role,
        Formula formula, string prose, bool literature = false) =>
        Describe.Lean(DescribeId.Create("kz38-kernel-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Analytic/KarpZhangNinh/Result." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula KernelAFormula()
    {
        Formula n = KernelX("n"), t = KernelX("t");
        return KernelAll("n", KernelN(), KernelAll("t", KernelR(), KernelEq(KernelCall("a", n, t),
            KernelCall("ite", KernelEq(n, D(0)), D(0),
                KernelDiv(KernelPoch(KernelMul(D(3), n), t), KernelFact(KernelNSub(KernelMul(D(3), n), D(1))))))));
    }

    private static Formula KernelRawFormula()
    {
        Formula mu=KernelX("mu"), alpha=KernelX("alpha"), beta=KernelX("beta"), m=KernelX("m"), k=KernelX("k");
        Formula expression=KernelSub(KernelMul(KernelCall("a", k, KernelAdd(mu,alpha)), KernelCall("a", KernelNSub(m,k), KernelAdd(mu,beta))),
            KernelMul(KernelCall("a", k, mu), KernelCall("a", KernelNSub(m,k), KernelAdd(KernelAdd(mu,alpha),beta))));
        return KernelParameters(KernelAll("m",KernelN(),KernelAll("k",KernelN(),KernelEq(KernelCall("raw",mu,alpha,beta,m,k),expression))));
    }

    private static Formula KernelPairedFormula()
    {
        Formula mu=KernelX("mu"), alpha=KernelX("alpha"), beta=KernelX("beta"), m=KernelX("m"), k=KernelX("k");
        Formula raw=KernelCall("raw",mu,alpha,beta,m,k);
        Formula other=KernelCall("raw",mu,alpha,beta,m,KernelNSub(m,k));
        return KernelParameters(KernelAll("m",KernelN(),KernelAll("k",KernelN(),KernelEq(KernelCall("paired",mu,alpha,beta,m,k),
            KernelCall("ite",KernelEq(KernelMul(D(2),k),m),raw,KernelAdd(raw,other))))));
    }

    private static Formula KernelPairFormula()
    {
        Formula a=KernelX("a"), b=KernelX("b"), c=KernelX("c"), n=KernelX("N"), k=KernelX("k");
        Formula value=KernelSub(KernelSub(KernelAdd(KernelMul(KernelPoch(k,KernelAdd(a,b)),KernelPoch(KernelNSub(n,k),KernelAdd(a,c))),
            KernelMul(KernelPoch(k,KernelAdd(a,c)),KernelPoch(KernelNSub(n,k),KernelAdd(a,b)))),
            KernelMul(KernelPoch(k,a),KernelPoch(KernelNSub(n,k),KernelAdd(KernelAdd(a,b),c)))),
            KernelMul(KernelPoch(k,KernelAdd(KernelAdd(a,b),c)),KernelPoch(KernelNSub(n,k),a)));
        return KernelABC(KernelAll("N",KernelN(),KernelAll("k",KernelN(),KernelEq(KernelCall("pairPoch",a,b,c,n,k),value))));
    }

    private static Formula KernelStepFormula()
    {
        Formula a=KernelX("a"), b=KernelX("b"), c=KernelX("c"), n=KernelX("N"), k=KernelX("k");
        Formula conclusion=KernelLt(KernelCall("pairPoch",a,b,c,n,KernelNSub(k,D(1))),D(0));
        conclusion=KernelImp(KernelLe(KernelCall("pairPoch",a,b,c,n,k),D(0)),conclusion);
        conclusion=KernelImp(KernelLe(KernelMul(D(2),k),n),conclusion);
        conclusion=KernelImp(KernelLe(D(1),k),conclusion);
        return KernelABC(KernelAll("N",KernelN(),KernelAll("k",KernelN(),KernelPositiveABC(conclusion))));
    }

    private static Formula KernelSignFormula()
    {
        Formula mu=KernelX("mu"),alpha=KernelX("alpha"),beta=KernelX("beta"),m=KernelX("m"),i=KernelX("i"),j=KernelX("j");
        Formula conclusion=KernelLe(D(0),KernelCall("paired",mu,alpha,beta,m,j));
        conclusion=KernelImp(KernelLt(D(0),KernelCall("paired",mu,alpha,beta,m,i)),conclusion);
        conclusion=KernelImp(KernelLt(i,j),conclusion);
        conclusion=KernelAll("j",KernelN(),KernelImp(KernelLe(j,new Formula.Apply(Seq(Operatorname,Grp(Seq(KernelX("Nat"),Dot,KernelX("div")))),[m,D(2)])),conclusion));
        conclusion=KernelAll("i",KernelN(),KernelImp(KernelLe(i,new Formula.Apply(Seq(Operatorname,Grp(Seq(KernelX("Nat"),Dot,KernelX("div")))),[m,D(2)])),conclusion));
        return KernelParameters(KernelAll("m",KernelN(),KernelImp(KernelLt(D(0),mu),KernelImp(KernelLt(D(0),alpha),KernelImp(KernelLt(D(0),beta),conclusion)))));
    }

    private static Formula KernelParameters(Formula f)=>KernelAll("mu",KernelR(),KernelAll("alpha",KernelR(),KernelAll("beta",KernelR(),f)));
    private static Formula KernelABC(Formula f)=>KernelAll("a",KernelR(),KernelAll("b",KernelR(),KernelAll("c",KernelR(),f)));
    private static Formula KernelPositiveABC(Formula f)=>KernelImp(KernelLt(D(0),KernelX("a")),KernelImp(KernelLt(D(0),KernelX("b")),KernelImp(KernelLt(D(0),KernelX("c")),f)));
    private static Formula KernelX(string name)=>F.Id(name);
    private static Formula KernelR()=>F.Id("Real");
    private static Formula KernelN()=>F.Id("Nat");
    private static Formula KernelCall(string name,params Formula[] args)=>new Formula.FunctionCall(FormulaIdentifier.Create(name),[..args]);
    private static Formula KernelAll(string name,Formula type,Formula body)=>new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(name),type,body);
    private static Formula KernelEq(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula KernelLt(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula KernelLe(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula KernelImp(Formula a,Formula b)=>new Formula.Logic(KernelParenthesized(a),FormulaLogicOperator.Implies,KernelParenthesized(b));
    private static Formula KernelAdd(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula KernelSub(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula KernelMul(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula KernelDiv(Formula a,Formula b)=>new Formula.Fraction(a,b);
    private static Formula KernelParenthesized(Formula a)=>Seq(Open,a,Close);
    private static Formula KernelFact(Formula n)=>Seq(KernelParenthesized(n),Bang);
    private static Formula KernelNSub(Formula a,Formula b)=>new Formula.Apply(Seq(Operatorname,Grp(Seq(KernelX("Nat"),Dot,KernelX("sub")))),[a,b]);
    private static Formula KernelPoch(Formula n,Formula t)=>new Formula.Apply(Seq(Operatorname,Grp(Seq(KernelX("Polynomial"),Dot,KernelX("eval")))),[t,KernelCall("ascPochhammer",KernelR(),n)]);
}
