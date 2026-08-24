using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.DynamicProgramming;

internal sealed class DiscountedBellmanContractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite-state finite-action discounted Bellman operator is a strict sup-norm "
            + "contraction with a unique fixed value function.",
        H("Discounted Bellman Contraction and Fixed Value"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("discounted-bellman-contraction-and-unique-fixed-value"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/DynamicProgramming/DiscountedBellmanContraction."
                        + "discounted_bellman_contraction_and_unique_fixed_point"),
                H("The discounted Bellman operator has one fixed value"),
                StatementSource.FromAuthor(ContractionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let the state and action spaces be finite and nonempty, with the state "
                            + "space discrete. Fix an arbitrary real reward, a nonnegative "
                            + "transition kernel whose weights sum to one for every state-action "
                            + "pair, and a discount factor gamma strictly between zero and one. "
                            + "The Bellman operator maximizes immediate reward plus discounted "
                            + "expected continuation value over all actions.")),
                    Paragraph(Text(
                        "Each transition row is a probability distribution, so changing the "
                            + "value function changes every continuation expectation by at most "
                            + "the uniform distance between the two value functions. Multiplication "
                            + "by gamma gives the actionwise bound, and taking the finite action "
                            + "maximum preserves it. Thus the full Bellman operator is gamma-"
                            + "Lipschitz in the uniform norm.")),
                    Paragraph(Text(
                        "Because gamma is strictly below one, this Lipschitz estimate is a strict "
                            + "contraction on the complete space of bounded continuous real-valued "
                            + "functions on the finite state space. The contraction fixed-point "
                            + "principle therefore supplies a fixed value function and forces every "
                            + "other fixed value function to equal it."))),
                DescribeRole.Theorem))));

    private static Formula ContractionFormula()
    {
        Formula state = F.Id("S");
        Formula action = F.Id("A");
        Formula statePoint = F.Id("s");
        Formula actionPoint = F.Id("a");
        Formula nextState = F.Id("t");
        Formula reward = F.Id("r");
        Formula transition = F.Id("P");
        Formula discount = GammaLower;
        Formula value = F.Id("v");
        Formula other = F.Id("w");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula nonnegativeReals = Seq(Operatorname, Grp(F.Id("NNReal")));
        Formula rewardType = Seq(
            state, Sp, Times, Sp, action, Sp, To, Sp, real);
        Formula transitionType = Seq(
            state, Sp, Times, Sp, action, Sp, Times, Sp, state, Sp, To, Sp, real);
        Formula valueSpace = Call("BoundedContinuousFunctions", state, real);
        Formula transitionValue = new Formula.Apply(
            transition, [statePoint, actionPoint, nextState]);
        Formula transitionNonnegative = Seq(
            Forall, Sp, statePoint, InMacro, Sp, state, Comma, Sp,
            actionPoint, InMacro, Sp, action, Comma, Sp,
            nextState, InMacro, Sp, state, Comma, Sp,
            D(0), Sp, Leq, Sp, transitionValue);
        Formula transitionNormalized = Seq(
            Forall, Sp, statePoint, InMacro, Sp, state, Comma, Sp,
            actionPoint, InMacro, Sp, action, Comma, Sp,
            Sum, Underscore, Grp(nextState, InMacro, Sp, state), Sp,
            transitionValue, Sp, Eq, Sp, D(1));
        Formula bellmanValue = Call(
            "discountedBellmanOperator", reward, transition, discount, value);
        Formula bellmanOther = Call(
            "discountedBellmanOperator", reward, transition, discount, other);
        Formula contraction = Seq(
            Forall, Sp, value, Comma, Sp, other, Colon, Sp, valueSpace, Comma, Sp,
            new Formula.Norm(Seq(bellmanValue, Sp, Minus, Sp, bellmanOther)),
            Sp, Leq, Sp, discount, Sp,
            new Formula.Norm(Seq(value, Sp, Minus, Sp, other)));
        Formula uniqueFixedValue = Seq(
            Exists, Bang, Sp, value, Colon, Sp, valueSpace, Comma, Sp,
            bellmanValue, Sp, Eq, Sp, value);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, action, Colon, Sp, type, Comma,
            RowBreak, Grp(),
            Call("FiniteNonempty", state), Comma, Sp,
            Call("DiscreteTopology", state), Comma, Sp,
            Call("FiniteNonempty", action), Comma,
            RowBreak, Grp(),
            reward, Colon, Sp, rewardType, Comma, Sp,
            transition, Colon, Sp, transitionType, Comma,
            RowBreak, Grp(),
            discount, Colon, Sp, nonnegativeReals, Comma, Sp,
            D(0), Sp, Lt, Sp, discount, Sp, Lt, Sp, D(1), Comma,
            RowBreak, Grp(),
            Open, transitionNonnegative, Sp, Land, Sp, transitionNormalized, Close,
            Sp, Rightarrow, Sp,
            RowBreak, Grp(),
            Open, contraction, Close, Sp, Land, Sp,
            Open, uniqueFixedValue, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
