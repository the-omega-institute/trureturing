using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KarpZhangCatalanPower;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/karpzhang2023pochhammer");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both coefficient signs of Karp and Zhang's Conjecture 4.2.",
        H("Catalan powers preserve the two sequence classes"), Blocks(
            Describe.Lean(DescribeId.Create("karp-zhang-catalan-log-convex"),
                DeclarationHandle.Create("D5/S3/Analytic/KarpZhangCatalanPower/Result.IsLogConvex"),
                H("Log-convex sequences"), StatementSource.FromAuthor(ConvexFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Definition 1.1, page 2: “Let {fₖ}ₖ₌₀∞ be a non-negative nontrivial real sequence.” The log-convex clause reads: “If fₖ² ≤ fₖ₋₁fₖ₊₁ for all k ∈ ℕ, the sequence is called log-convex (this inequality implies that a nontrivial sequence is strictly positive).”")),
                    Paragraph(Text("Here the natural indices in the inequality start at one. The predicate keeps nonnegativity and nontriviality and imposes no interval-support condition. The literal inequalities also admit a sequence supported on {0}; that endpoint case is included. The log-concave class is the existing KarpZhangReciprocal.Result.IsLogConcave, including its interval-support condition."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("karp-zhang-catalan-delta"),
                DeclarationHandle.Create("D5/S3/Analytic/KarpZhangCatalanPower/Result.delta"),
                H("The finite Turanian coefficient"), StatementSource.FromAuthor(DeltaFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The coefficient a is Coeff.a, the literal quotient (t) rising factorial 2k divided by (t+1) rising factorial k times k factorial. The finite sum is the degree-m Cauchy coefficient; neither convergence nor growth assumptions on h are needed."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("karp-zhang-catalan-claim"),
                DeclarationHandle.Create("D5/S3/Analytic/KarpZhangCatalanPower/Result.claim"),
                H("Conjecture 4.2"), StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Conjecture 4.2, page 8: Assume that {hₖ}ₖ₌₀∞ is log-concave (log-convex ) and independent of µ. Then the function µ → h(µ; x) defined in (15) is coefficient-wise log-concave (log-convex ).")),
                    Paragraph(Text("For every sequence h, nonnegative real mu, alpha and beta, and every natural coefficient degree, delta is nonnegative for the source's log-concave class and nonpositive for its log-convex class. The sequence is independent of the parameters because a single h is fixed before they are quantified."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("karp-zhang-catalan-result"),
                DeclarationHandle.Create("D5/S3/Analytic/KarpZhangCatalanPower/Result.result"),
                H("Both signs hold in every degree"), StatementSource.FromAuthor(Disp(F.Id("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The index law makes the full kernel sum zero. The positive derivative generator and reflected-interval cancellation give nonnegative central tails, including mu=0. The generic Abel identity KarpZhangReciprocal.Result.abel_layers writes delta as the increments of h(k)h(m-k) times these tails.")),
                    Paragraph(Text("For log-concavity, KarpZhangReciprocal.Result.balanced_step makes the increments nonnegative. For log-convexity, a zero at index one propagates to every positive index. Otherwise all entries are positive, the adjacent inequalities make successive ratios increase, and the balanced products decrease. Thus their increments are nonpositive. This includes finite and singleton log-concave supports and the log-convex sequence supported only at zero. The central term is counted once and the degrees zero and one require no special assumption."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("karp-zhang-2023-conjecture-4-2"),
                    ResolutionKind.Proved)))));

    private static Formula ConvexFormula()
    {
        Formula h = F.Id("h");
        Formula k = F.Id("k");
        Formula nonnegative = All("k", F.Id("Nat"), Le(Num(0), App(h, k)));
        Formula nontrivial = new Formula.Bind(FormulaQuantifier.Exists,
            FormulaIdentifier.Create("k"), F.Id("Nat"),
            new Formula.Relation(App(h, k), FormulaRelationOperator.NotEqual, Num(0)));
        Formula local = All("k", F.Id("Nat"), Implies(Le(Num(1), k),
            Le(new Formula.Power(App(h, k), Num(2)), Multiply(App(h, Subtract(k, Num(1))), App(h, Add(k, Num(1)))))));
        return Disp(All("h", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")),
            Iff(App(F.Id("IsLogConvex"), h), And(nonnegative, And(nontrivial, local)))));
    }

    private static Formula DeltaFormula()
    {
        Formula h = F.Id("h");
        Formula m = F.Id("m");
        Formula k = F.Id("k");
        Formula mu = F.Id("mu");
        Formula alpha = F.Id("alpha");
        Formula beta = F.Id("beta");
        Formula term = Multiply(Multiply(App(h, k), App(h, Subtract(m, k))),
            Subtract(Multiply(App(Q("Coeff", "a"), k, Add(mu, alpha)),
                    App(Q("Coeff", "a"), Subtract(m, k), Add(mu, beta))),
                Multiply(App(Q("Coeff", "a"), k, mu),
                    App(Q("Coeff", "a"), Subtract(m, k), Add(Add(mu, alpha), beta)))));
        Formula sum = Seq(Sum, Underscore, Grp(k, Sp, InMacro, Sp,
            App(Q("Finset", "range"), Add(m, Num(1)))), Sp, term);
        return Disp(All("h", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")),
            All("mu", F.Id("Real"), All("alpha", F.Id("Real"), All("beta", F.Id("Real"),
                All("m", F.Id("Nat"), Equal(App(F.Id("delta"), h, mu, alpha, beta, m), sum)))))));
    }

    private static Formula ClaimFormula()
    {
        Formula h = F.Id("h");
        Formula mu = F.Id("mu");
        Formula alpha = F.Id("alpha");
        Formula beta = F.Id("beta");
        Formula d = App(F.Id("delta"), h, mu, alpha, beta, F.Id("m"));
        Formula assertion = All("h", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")),
            All("mu", F.Id("Real"), All("alpha", F.Id("Real"), All("beta", F.Id("Real"),
                All("m", F.Id("Nat"), Implies(Le(Num(0), mu), Implies(Le(Num(0), alpha),
                    Implies(Le(Num(0), beta), And(
                        Implies(App(Q("KarpZhangReciprocal", "Result", "IsLogConcave"), h), Le(Num(0), d)),
                        Implies(App(F.Id("IsLogConvex"), h), Le(d, Num(0))))))))))));
        return Disp(Iff(F.Id("claim"), assertion));
    }

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Q(string a, string b) => Seq(Operatorname, Grp(F.Id(a)), Dot, Operatorname, Grp(F.Id(b)));
    private static Formula Q(string a, string b, string c) => Seq(Q(a, b), Dot, Operatorname, Grp(F.Id(c)));
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
}
