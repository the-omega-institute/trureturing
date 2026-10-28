using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class ActualIntegerHeightJumpDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ActualIntegerHeightJump.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual maximal occupied prime powers control Robin height jumps and genuine least-crossing overshoot.",
        H("Actual Integer Height Jumps"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-divisor-log"), DeclarationHandle.Create(Prefix + "divisorLog"),
                H("The actual divisor-sum logarithm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural n, divisorLog(n)=log(sigma(1,n)/n). The expression is "
                    + "totalized by Lean at zero; arithmetic applications below prove positivity of n."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-robin-height"), DeclarationHandle.Create(Prefix + "actualHeight"),
                H("The original scaled excess"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every real eta and natural n, actualHeight(eta,n)=(log(n))^eta "
                    + "times (originalObjective(n)-gamma), using real powers and the literal "
                    + "sigma/log objective. First crossings are restricted to n>=3."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("maximal-occupied-prime-power"),
                DeclarationHandle.Create(Prefix + "MaximalPrimePower"),
                H("All maximizing prime-power choices"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For natural m,q, MaximalPrimePower(m,q) means q belongs to the actual "
                    + "prime-factor set of m and p^(m.factorization(p))<=q^(m.factorization(q)) "
                    + "for every p in that set. All ties remain included."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("eventual-actual-integer-height-jump"),
                DeclarationHandle.Create(Prefix + "eventual_actual_height_jump"),
                H("Uniform control for every maximal occupied prime power"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real 0<eta<1/2 there is one real A>1 such that every "
                        + "positive natural m with log(m)>=A and originalObjective(m)>gamma "
                        + "has a maximal occupied prime-power choice. For every such q, put "
                        + "n=m/q, X=log(m), Y=log(n), delta=W(m)-W(n). Then n>=3, delta>0, "
                        + "H(eta,m)-H(eta,n)<=X^eta*delta<=X^(eta-1)*log(X). "
                        + "The threshold is independent of m and of the maximizing choice q.")),
                    Paragraph(Text(
                        "With Q=q^(m.factorization(q)), the actual factorization and the "
                        + "cardinality of its prime support imply X<=Q*log(Q). Splitting "
                        + "Q>=X and Q<X gives 1/Q<=log(X)/X eventually. The existing exact "
                        + "single-layer objective delta and geometric marginal bound give "
                        + "0<delta<=1/Q for the actual integer quotient. The elementary "
                        + "sigma(1,n)<=n^2 yields W(n)<=Y, whereas positivity at m gives "
                        + "W(n)>log(log(X))+gamma-delta. Thus Y exceeds every fixed bound "
                        + "uniformly before the coefficient-two envelope is used at n.")),
                    Paragraph(Text(
                        "Write L=log(X), l=log(Y), E=originalObjective(n)-gamma. The new "
                        + "integer envelope gives E<=2/l, while positivity at m gives "
                        + "log(L/l)<2/l+delta. Consequently 2*eta*L<=l eventually for each "
                        + "original eta<1/2. With beta=log(X)-log(Y) and r=(Y/X)^eta, "
                        + "the exponential tangent gives 0<=1-r<=eta*beta and the logarithmic "
                        + "tangent gives beta/L<=log(L)-log(l). Therefore "
                        + "E*(1-r)<=log(L)-log(l), including negative E. Substitution into "
                        + "the exact height difference proves the asserted bound. No assumption "
                        + "that Y/X tends to one, stronger Robin envelope, RH, or special "
                        + "choice among ties is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-least-crossing-overshoot"),
                DeclarationHandle.Create(Prefix + "first_crossing_calibration"),
                H("Cofinal least crossings have vanishing overshoot"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix any real 0<eta<1/2. Assume explicitly that for every real T "
                        + "there is a natural m>=3 with H(eta,m)>=T. There is a function "
                        + "crossing from real thresholds to natural integers such that, for "
                        + "every T, crossing(T)>=3, H(eta,crossing(T))>=T, and every natural "
                        + "3<=n<crossing(T) has H(eta,n)<T. Thus these are actual least "
                        + "integer crossings, not an artificial sequence.")),
                    Paragraph(Text(
                        "As T tends to infinity, crossing(T) tends to infinity. If "
                        + "X(T)=log(crossing(T)), the explicit error X(T)^(eta-1)*log(X(T)) "
                        + "tends to zero. Eventually T<=H(eta,crossing(T))<T+that error, "
                        + "and H(eta,crossing(T))-T tends to zero. The finite maximum of "
                        + "the actual heights on each initial integer segment pays cofinality. "
                        + "A maximal-prime-power divisor n=m/q is eventually at least three "
                        + "and precedes the least crossing, so the preceding jump theorem "
                        + "bounds its overshoot. The standard logarithm versus real-power "
                        + "limit supplies the vanishing error.")),
                    Paragraph(Text(
                        "These are repository-derived arithmetic connections to the existing "
                        + "fixed-price, Mertens and Euler-layer inputs at immutable revision "
                        + "16c3ea75a9347e03a4401e66b911cef405ba17df, with no literature priority "
                        + "claim. Unboundedness is an original oscillation input, not a newly "
                        + "proved fact. Signed upper estimates, fixed-height cofinal left "
                        + "envelopes, long low intervals, the full record argument and RH "
                        + "remain outside these conclusions."))),
                DescribeRole.Theorem))));
}
