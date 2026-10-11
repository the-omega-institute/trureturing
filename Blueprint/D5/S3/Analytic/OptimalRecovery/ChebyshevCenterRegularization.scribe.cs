using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.OptimalRecovery;

internal sealed class ChebyshevCenterRegularizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/OptimalRecovery/ChebyshevCenterRegularization.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Estimation/foucartliao2024sprocedure");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A real Chebyshev center need not minimize any positively weighted quadratic regularization objective.",
        H("Foucart–Liao Chebyshev-Center Regularization Refutation"),
        Blocks(
            Entry("feasible-set", "feasible", "Model and measurement constraints", Feasible(),
                "For linear P:ℝⁿ→ℝⁿ and Λ:ℝⁿ→ℝᵐ, data y∈ℝᵐ and bounds ε,η∈ℝ, "
                + "the feasible set consists of f with ‖Pf‖≤ε and ‖y−Λf‖≤η. "
                + "The norms are Euclidean. Section 5 uses Q=Id and equal bounds ε=η; "
                + "the counterexample also has equal bounds.", DescribeRole.Definition, true),
            Entry("chebyshev-center", "IsChebyshevCenter", "Comparison with every enclosing bound", Center(),
                "In a normed additive commutative group E, c is a Chebyshev center of C when every "
                + "uniform real distance bound for every competing center c′ also bounds distances from c. "
                + "For the nonempty bounded Euclidean feasible sets in the assertion, this expresses "
                + "minimization of the worst-case reconstruction distance.", DescribeRole.Definition, true),
            Entry("regularizer", "IsRegularizer", "Quadratic regularization", Regularizer(),
                "The predicate states global minimization over all f∈ℝⁿ of "
                + "(1−τ)‖Pf‖²+τ‖y−Λf‖², as in equation (8). "
                + "The predicate itself allows any real τ; the assertion requires 0<τ<1.",
                DescribeRole.Definition, true),
            Entry("regularization-claim", "claim", "Every real center is a regularizer", Claim(),
                "Section 5, Question 2, asks verbatim: “Is the Chebyshev center always obtained via regularization?” "
                + "The authors explain: “From [10], we know that the answer is affirmative under the specific "
                + "conditions mentioned above, since the Chebyshev center equals the regularizer f_{τ♯} "
                + "with parameter τ♯∈(0,1) satisfying the implicit equation (9). Without the specific conditions, "
                + "we also know from [8] that the answer is affirmative if one considered the complex setting "
                + "rather than the real setting.” The specific conditions are that P is an orthogonal projector "
                + "and ΛΛ*=Idₘ. The displayed assertion quantifies over finite-dimensional real Euclidean "
                + "spaces and arbitrary linear P and Λ, positive bounds ε,η, and every center of each "
                + "nonempty bounded feasible set. The example uses ε=η=1 and an orthogonal projector, "
                + "so the negation also addresses the source's equal-bound setting.", DescribeRole.Definition, true),
            Entry("refutation", "result", "A center outside every regularization parameter", Disp(Seq(Neg, Sp, V("claim"))),
                "Take H=ℝ², P=diag(1,0), Λ(x,z)=((x−z)/2,z), y=(1,0) and ε=η=1. "
                + "The map P is an orthogonal projector and Λ is invertible, while "
                + "ΛΛ* has rows (1/2,−1/2) and (−1/2,1), so ΛΛ*≠Id₂. "
                + "The feasible set is x²≤1 and g=(x−z−2)²+4z²−4≤0. "
                + "For c*=(3/5,−1/5), put q=(x−3/5)²+(z+1/5)²−4/5. "
                + "The identity 10(4−x+z)q=(x−1)(4−x+7z)²+(17−11x+2z)g, "
                + "with 4−x+z>0 and 17−11x+2z≥0 on the feasible set, proves q≤0. "
                + "The feasible contact points A=(1,3/5), B=(−1/5,−3/5), D=(1,−1) "
                + "have weights 5/12,1/3,1/4 and satisfy "
                + "(5/12)‖A−c‖²+(1/3)‖B−c‖²+(1/4)‖D−c‖²=4/5+‖c−c*‖². "
                + "Consequently c* is the unique center and its radius is √(4/5). "
                + "The comparator v=(3/5,−7/25) has ‖Pv‖²=‖Pc*‖²=9/25 but "
                + "‖y−Λv‖²=49/125<50/125=‖y−Λc*‖². "
                + "For every τ>0 the objective is smaller at v by τ/125. More generally, "
                + "no objective a‖Pf‖²+b‖y−Λf‖² with b>0 has c* as a minimizer. "
                + "The private lemmas feasible_coordinates, contacts and bounded establish the coordinate "
                + "constraints and admissibility; containment proves the enclosing-ball bound, "
                + "center_certificate uses the weighted contact identity, and not_regularizer supplies "
                + "the strict comparison. The proof uses exact rational arithmetic. "
                + "The radius and uniqueness follow from containment and the weighted identity; "
                + "they are not separate public theorems. The conclusion concerns the real setting "
                + "and does not contradict the affirmative complex result or the real result under "
                + "both specific conditions. It makes no exhaustive priority claim about earlier "
                + "work on intersections of two ellipsoids.", DescribeRole.Theorem, false))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("foucart-liao-2024-chebyshev-center-regularization"),
                ResolutionKind.Refuted) : null);

    private static Formula V(string name) => name switch
    {
        "Λ" => Lambda,
        "ε" => Varepsilon,
        "η" => Seq(Mathrm, Grp(F.Id("eta"))),
        "τ" => Tau,
        "c′" => Seq(F.Id("c"), Apos),
        _ => F.Id(name)
    };
    private static Formula P(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula At(Formula value, Formula arg) => new Formula.Apply(value, [arg]);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Euclidean(string dimension) => Call("EuclideanSpace", Real, Call("Fin", V(dimension)));
    private static Formula Linear(Formula domain, Formula codomain) => Call("LinearMap", Real, domain, codomain);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Leq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Less(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(P(x), FormulaLogicOperator.And, P(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(P(x), FormulaLogicOperator.Implies, P(y));
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, P(y));
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Norm(Formula value) => Seq(Vert, Sp, value, Vert);
    private static Formula Square(Formula value) => new Formula.Power(value, D(2));
    private static Formula Member(Formula x, Formula set) => Seq(x, Sp, InMacro, Sp, set);
    private static Formula FeasibleSet => Call("feasible", V("P"), V("Λ"), V("y"), V("ε"), V("η"));
    private static Formula Objective(Formula f) => Add(
        Mul(P(Sub(D(1), V("τ"))), Square(Norm(At(V("P"), f)))),
        Mul(V("τ"), Square(Norm(Sub(V("y"), At(V("Λ"), f))))));

    private static Formula Feasible() => Disp(Iff(Member(V("f"), FeasibleSet),
        And(Leq(Norm(At(V("P"), V("f"))), V("ε")),
            Leq(Norm(Sub(V("y"), At(V("Λ"), V("f")))), V("η")))));

    private static Formula Center()
    {
        Formula Bound(Formula c) => All("f", V("E"),
            Imp(Member(V("f"), V("C")), Leq(Norm(Sub(V("f"), c)), V("M"))));
        return Disp(Iff(Call("IsChebyshevCenter", V("C"), V("c")),
            All("c′", V("E"), All("M", Real, Imp(Bound(V("c′")), Bound(V("c")))))));
    }

    private static Formula Regularizer() => Disp(Iff(
        Call("IsRegularizer", V("P"), V("Λ"), V("y"), V("τ"), V("c")),
        All("f", Euclidean("n"), Leq(Objective(V("c")), Objective(V("f"))))));

    private static Formula Claim()
    {
        Formula conclusion = Ex("τ", Real, And(And(Less(D(0), V("τ")), Less(V("τ"), D(1))),
            Call("IsRegularizer", V("P"), V("Λ"), V("y"), V("τ"), V("c"))));
        Formula centers = All("c", Euclidean("n"),
            Imp(Call("IsChebyshevCenter", FeasibleSet, V("c")), conclusion));
        Formula body = Imp(Less(D(0), V("ε")), Imp(Less(D(0), V("η")),
            Imp(Call("Nonempty", FeasibleSet), Imp(Call("IsBounded", FeasibleSet), centers))));
        return Disp(Iff(V("claim"), All("n", Nat, All("m", Nat,
            All("P", Linear(Euclidean("n"), Euclidean("n")),
            All("Λ", Linear(Euclidean("n"), Euclidean("m")),
            All("y", Euclidean("m"), All("ε", Real, All("η", Real, body)))))))));
    }
}
