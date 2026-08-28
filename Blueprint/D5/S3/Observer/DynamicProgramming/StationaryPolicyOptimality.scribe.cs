using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.DynamicProgramming;

internal sealed class StationaryPolicyOptimalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula state = F.Id("S");
        Formula action = F.Id("A");
        Formula statePoint = F.Id("s");
        Formula actionPoint = F.Id("a");
        Formula nextState = F.Id("t");
        Formula loss = F.Id("ell");
        Formula transition = F.Id("P");
        Formula discount = GammaLower;
        Formula value = F.Id("v");
        Formula valueStar = Seq(F.Id("V"), Caret, Grp(Star));
        Formula policyValue = Seq(F.Id("V"), Caret, Grp(F.Id("pi")));
        Formula policy = F.Id("pi");
        Formula lossAt = new Formula.Apply(loss, [statePoint, actionPoint]);
        Formula transitionAt = new Formula.Apply(
            transition, [statePoint, actionPoint, nextState]);
        Formula valueAt = new Formula.Apply(value, [nextState]);
        Formula continuation = Seq(
            Sum, Underscore, Grp(nextState, InMacro, Sp, state), Sp,
            transitionAt, Sp, Times, Sp, valueAt);
        Formula lossBellmanAt = Call(
            "LossBellman", loss, transition, discount, value, statePoint);
        Formula lossMinimum = Seq(
            Operatorname, Grp(F.Id("inf")), Underscore,
            Grp(actionPoint, InMacro, Sp, action), Sp, Open,
            lossAt, Sp, Plus, Sp, discount, Sp, continuation, Close);
        Formula lossFormula = Disp(Seq(lossBellmanAt, Sp, Eq, Sp, lossMinimum, Dot));
        Formula fixedOptimal = Call("Fixed", F.Id("T"), valueStar);
        Formula fixedPolicy = Call("Fixed", F.Id("Tpi"), policyValue);
        Formula greedy = Call("GreedyEverywhere", policy, valueStar);
        Formula optimal = Seq(policyValue, Sp, Eq, Sp, valueStar);
        Formula zeroFormula = Disp(Seq(
            discount, Sp, Eq, Sp, D(0), Sp, Land, Sp,
            fixedOptimal, Sp, Land, Sp, fixedPolicy, Sp, Land, Sp,
            greedy, Sp, Rightarrow, Sp, optimal, Dot));
        Formula mainFormula = Disp(Seq(
            D(0), Sp, Leq, Sp, discount, Sp, Lt, Sp, D(1), Sp, Land, Sp,
            Call("Stochastic", transition), Sp, Land, Sp,
            fixedOptimal, Sp, Land, Sp, fixedPolicy, Sp, Land, Sp,
            greedy, Sp, Rightarrow, Sp, optimal, Dot));
        Formula reachableFormula = Disp(Seq(
            Call("ReachableFrom", policy, F.Id("false")), Sp, Eq, Sp,
            OpenBrace, F.Id("false"), CloseBrace, Sp, Land, Sp,
            Call("GreedyOnReachable", policy, F.Id("false")), Sp, Land, Sp,
            Call("PolicyValue", policy, F.Id("true")), Sp, Eq, Sp, D(2), Sp, Land, Sp,
            Call("OptimalValue", F.Id("true")), Sp, Eq, Sp, D(0), Dot));
        Formula discountNecessaryFormula = Disp(Seq(
            discount, Sp, Eq, Sp, D(1), Sp, Land, Sp,
            Call("Fixed", F.Id("Tpi"), D(0)), Sp, Land, Sp,
            Call("Fixed", F.Id("Tpi"), D(1)), Sp, Land, Sp,
            D(0), Sp, Neq, Sp, D(1), Dot));
        Formula emptyFormula = Disp(Seq(
            Call("Empty", state), Sp, Rightarrow, Sp,
            Forall, Sp, policyValue, Comma, Sp, valueStar, Comma, Sp,
            policyValue, Sp, Eq, Sp, valueStar, Dot));
        Formula singletonFormula = Disp(Seq(
            action, Sp, Eq, Sp, OpenBrace, actionPoint, CloseBrace, Sp,
            Rightarrow, Sp, Forall, Sp, policy, Comma, Sp,
            Call("GreedyEverywhere", policy, value), Dot));
        Formula half = Seq(Frac, Grp(D(1)), Grp(D(2)));
        Formula constantFormula = Disp(Seq(
            state, Sp, Eq, Sp, OpenBrace, statePoint, CloseBrace, Sp, Land, Sp,
            loss, Sp, Eq, Sp, D(3), Sp, Land, Sp,
            discount, Sp, Eq, Sp, half, Sp, Rightarrow, Sp,
            Forall, Sp, policy, Comma, Sp,
            Call("PolicyValue", policy), Sp, Eq, Sp,
            Call("OptimalValue"), Sp, Eq, Sp, D(6), Dot));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Bellman-greedy stationary policies have the optimal discounted value, "
                + "with sharp global-state and discount hypotheses.",
            H("Stationary Policy Optimality"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("loss-bellman-pointwise-minimum"),
                    DeclarationHandle.Create(
                        "D5/S3/Observer/DynamicProgramming/StationaryPolicyOptimality."
                            + "discounted_loss_bellman_operator_apply"),
                    H("The loss Bellman operator is a finite minimum"),
                    StatementSource.FromAuthor(lossFormula),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Sign conjugation turns the existing finite reward maximum into "
                            + "immediate loss plus discounted continuation, minimized over "
                            + "the finite action set."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("zero-discount-greedy-policy-optimal"),
                    DeclarationHandle.Create(
                        "D5/S3/Observer/DynamicProgramming/StationaryPolicyOptimality."
                            + "zero_discount_greedy_stationary_policy_is_optimal"),
                    H("Greed remains sufficient at zero discount"),
                    StatementSource.FromAuthor(zeroFormula),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "At zero discount the continuation value disappears. The policy "
                            + "operator is constant, so its fixed value equals the greedy "
                            + "optimal fixed value without any stochastic-kernel premise."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("bellman-greedy-stationary-policy-optimal"),
                    DeclarationHandle.Create(
                        "D5/S3/Observer/DynamicProgramming/StationaryPolicyOptimality."
                            + "bellman_greedy_stationary_policy_is_optimal"),
                    H("Everywhere Bellman-greedy stationary policies are optimal"),
                    StatementSource.FromAuthor(mainFormula),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "This is a finite-state ordinary-MDP formalization, not a "
                                + "belief-simplex formalization. The policy selects an action "
                                + "at every state and realizes the Bellman loss minimum there.")),
                        Paragraph(Text(
                            "Greed makes the optimal value a fixed point of the fixed-policy "
                                + "operator. The existing discounted Bellman contraction theorem, "
                                + "instantiated with the singleton chosen action, makes that fixed "
                                + "point unique. Hence the policy value equals the optimal "
                                + "value."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("reachable-only-greed-not-global"),
                    DeclarationHandle.Create(
                        "D5/S3/Observer/DynamicProgramming/StationaryPolicyOptimality."
                            + "reachable_only_greed_does_not_imply_global_optimality"),
                    H("Reachable-only greed is not global optimality"),
                    StatementSource.FromAuthor(reachableFormula),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Two self-loop states make true unreachable from the initial false "
                            + "state. The policy is greedy at false but incurs value two at true, "
                            + "whereas the globally optimal value is zero."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("strict-discount-bound-necessary"),
                    DeclarationHandle.Create(
                        "D5/S3/Observer/DynamicProgramming/StationaryPolicyOptimality."
                            + "discount_factor_lt_one_is_necessary"),
                    H("The strict discount bound is necessary"),
                    StatementSource.FromAuthor(discountNecessaryFormula),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "At discount one, the one-state zero-loss self-loop policy operator is "
                            + "the identity and therefore fixes both zero and one. Fixed-point "
                            + "value uniqueness, and thus this proof of policy optimality, "
                            + "fails."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("empty-state-policy-values-equal"),
                    DeclarationHandle.Create(
                        "D5/S3/Observer/DynamicProgramming/StationaryPolicyOptimality."
                            + "empty_state_policy_values_equal"),
                    H("Empty-state policy optimality is vacuous"),
                    StatementSource.FromAuthor(emptyFormula),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Every two bounded functions on the empty state type are extensionally "
                            + "equal, so no state nonemptiness assumption belongs in the policy "
                            + "optimality conclusion."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("singleton-action-greed-automatic"),
                    DeclarationHandle.Create(
                        "D5/S3/Observer/DynamicProgramming/StationaryPolicyOptimality."
                            + "singleton_action_policy_is_automatically_greedy"),
                    H("A singleton action set makes greed automatic"),
                    StatementSource.FromAuthor(singletonFormula),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "With one action, the policy operator and the action-minimizing Bellman "
                            + "operator are definitionally the same finite minimum."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("constant-loss-all-policies-optimal"),
                    DeclarationHandle.Create(
                        "D5/S3/Observer/DynamicProgramming/StationaryPolicyOptimality."
                            + "constant_loss_single_state_all_policies_are_optimal"),
                    H("Constant loss makes every policy optimal in the singleton model"),
                    StatementSource.FromAuthor(constantFormula),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For one self-loop state, constant loss three, and half discount, every "
                            + "action has the same Bellman value six. Thus every policy is greedy "
                            + "and has the same value; the greed condition is automatic, not "
                            + "false."))),
                    DescribeRole.Theorem))));
    }
}
