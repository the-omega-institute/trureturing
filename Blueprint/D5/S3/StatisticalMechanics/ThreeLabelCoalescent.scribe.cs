using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class ThreeLabelCoalescentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/ThreeLabelCoalescent.";
    private static Formula Q(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        Seq(Q(name), Open, Join(args), Close);
    private static Formula Join(Formula[] args) => args.Length switch
    {
        0 => Seq(),
        1 => args[0],
        _ => Seq(args[0], Comma, Join(args[1..]))
    };
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, To, b);
    private static Formula Mass => Arrow(Call("Fin", D(5)), R);
    private static Formula Trajectory => Arrow(R, Mass);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A labelled pure coalescence chain on the five partitions of three labels.",
        H("Three-label pure coalescence"),
        Blocks(
            Paragraph(Text("The state order is N = 1|2|3, A = 12|3, B = 23|1, T = 123, C = 13|2. "
                + "The nonzero rates are N to A: 3, N to B: 1, N to C: 1/4, N to T: h, "
                + "A to T: 1/4, B to T: 17/4+h, and C to T: 1/4. T is absorbing. "
                + "The initial vector is (1,0,0,0,0). ForwardLaw requires this initial vector and "
                + "the five componentwise differential equations for every nonnegative real time; "
                + "it contains no closed-form equation. Write K = 4+h, ell = 17/4+h, "
                + "u = exp(-t/4), and v = exp(-ell*t).")),
            Paragraph(Text("The candidate vector explicit(h,t) is "
                + "(v,3(u-v)/K,t*v,1-v-3(u-v)/K-t*v-(u-v)/(4K),(u-v)/(4K)). "
                + "The association determinant delta(q) is q(N)q(T)-q(A)q(B). "
                + "The scalar H(h,t) is 1-((13/4+3t)/K)u-((h+3/4+(1+h)t)/K)v.")),
            Describe.Lean(
                DescribeId.Create("three-label-forward-solution"),
                DeclarationHandle.Create(Prefix + "forward_solution"),
                H("The forward equations determine the five masses and association"),
                StatementSource.FromAuthor(Disp(SolutionFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Uniqueness is applied successively to N, A, B and C, then T. "
                    + "Each difference solves a scalar homogeneous linear equation with zero initial value. "
                    + "The checked candidate therefore equals any solution of the original forward system. "
                    + "Substituting its five masses gives delta = v H. "
                    + "The resonant transition N to B produces the factor t v."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("three-label-positive-probability"),
                DeclarationHandle.Create(Prefix + "positive_probability_solution"),
                H("A strictly positive probability law at every positive time"),
                StatementSource.FromAuthor(Disp(ProbabilityFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The explicit vector solves the initial-value problem. At positive time, "
                    + "u exceeds v, so the masses at N, A, B and C are positive. The derivative of the T mass "
                    + "is a sum of nonnegative incoming flows, with strictly positive direct flow h times "
                    + "the N mass. Thus T grows strictly from zero. The five masses sum to one."))),
                DescribeRole.Theorem),
            Paragraph(Text("For V = 35/16+Kh and W = ell(1+h), set "
                + "G(h,t) = 3t/4-35/16+(V+Wt)exp(-Kt). Differentiation gives H' = uG/K and "
                + "G'' = K exp(-Kt)(KV-2W+KWt). The coefficient KV-2W equals "
                + "1/4+123h/16+6h squared+h cubed, so G is strictly convex on nonnegative time.")),
            Describe.Lean(
                DescribeId.Create("three-label-at-most-two-zeros"),
                DeclarationHandle.Create(Prefix + "no_three_positive_zeros"),
                H("At most two distinct positive association zeros"),
                StatementSource.FromAuthor(Disp(NoThreeFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Three positive determinant zeros would, together with H(0)=0, "
                    + "give three distinct zeros of H' by Rolle's theorem. Because u and K are positive, "
                    + "these would be three distinct zeros of G. Strict convexity makes the middle value "
                    + "strictly smaller than the maximum of the two outer zero values, a contradiction. "
                    + "This zero-count bound does not assert existence, simplicity or a critical parameter."))),
                DescribeRole.Theorem)
        )));

    private static Formula SolutionFormula()
    {
        Formula h = F.Id("h"), p = F.Id("p"), t = F.Id("t");
        Formula body = And(Eq(Seq(p, Open, t, Close), Call("explicit", h, t)),
            Eq(Call("delta", Seq(p, Open, t, Close)), Mul(Call("v", h, t), Call("H", h, t))));
        return All("h", R, Imp(Lt(D(0), h), All("p", Trajectory,
            Imp(Call("ForwardLaw", h, p), All("t", R, Imp(Le(D(0), t), body))))));
    }
    private static Formula ProbabilityFormula()
    {
        Formula h = F.Id("h"), p = F.Id("p"), t = F.Id("t"), i = F.Id("i");
        Formula q = Seq(p, Open, t, Close);
        Formula normalization = Eq(Seq(Sum, new Formula.Subscript(Seq(i, In, Call("Fin", D(5))))),
            Seq(p, Open, t, Comma, i, Close)), D(1));
        Formula positive = All("i", Call("Fin", D(5)), Lt(D(0), Seq(p, Open, t, Comma, i, Close)));
        Formula conclusion = And(Eq(q, Call("explicit", h, t)), And(normalization,
            And(positive, Eq(Call("delta", q), Mul(Call("v", h, t), Call("H", h, t))))));
        return All("h", R, Imp(Lt(D(0), h),
            And(Call("ForwardLaw", h, Call("explicit", h)),
                All("p", Trajectory, Imp(Call("ForwardLaw", h, p),
                    All("t", R, Imp(Lt(D(0), t), conclusion)))))));
    }

    private static Formula NoThreeFormula()
    {
        Formula h = F.Id("h"), p = F.Id("p"), a = F.Id("a"), b = F.Id("b"), c = F.Id("c");
        Formula Delta(Formula t) => Call("delta", Seq(p, Open, t, Close));
        Formula premise = And(Lt(D(0), a), And(Lt(a, b), And(Lt(b, c),
            And(Eq(Delta(a), D(0)), Eq(Delta(b), D(0))))));
        Formula nonzero = new Formula.Relation(Delta(c), FormulaRelationOperator.NotEqual, D(0));
        return All("h", R, Imp(Lt(D(0), h), All("p", Trajectory,
            Imp(Call("ForwardLaw", h, p), All("a", R, All("b", R,
                All("c", R, Imp(premise, nonzero))))))));
    }

}
