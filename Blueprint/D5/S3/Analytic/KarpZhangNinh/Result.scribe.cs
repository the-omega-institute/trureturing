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
            Describe.Lean(DescribeId.Create("karp-zhang-ninh-delta"),
                DeclarationHandle.Create("D5/S3/Analytic/KarpZhangNinh/Result.delta"),
                H("The Turanian coefficient"), StatementSource.FromAuthor(DeltaFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The source defines the Turanian as f(mu+alpha;x)f(mu+beta;x)-f(mu;x)f(mu+alpha+beta;x). Its coefficientwise convention, page 2, is: “if the coefficients δₖ at all powers of x in (2) are non-negative (non-positive) for all α, β ≥ 0 we will say that µ → f(µ; x) is coefficient-wise log-concave”. Here Kernel.a has zero constant coefficient, so the endpoint summands vanish. A single coefficient sequence is fixed independently of all three real parameters."))),
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
}
