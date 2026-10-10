using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource.ActualReserve;

internal sealed class ActualReservePrimeMaskDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResource/ActualReserve/ActualReservePrimeMask.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An arbitrary finite actual prime mask lower-bounds the same unrestricted reserve and the complete integer gap.",
        H("Actual Unrestricted Prime Mask Reserve"),
        Blocks(
            Paragraph(Text("Fix a real x > 1 and lambda_x = 1/(x log x). The actual objective is "
                + "J_x(n) = log(sigma(n)/n) - lambda_x log n for every n >= 1. "
                + "M(x) is the supremum over all those integers, including the unit. "
                + "With the inclusive harmonic reference F(x) = P(x) - lambda_x psi(x), "
                + "Res(x) = F(x) - M(x) and d_x(n) = M(x) - J_x(n). "
                + "Both use precisely the same objective, price, integer and unrestricted pressure.")),
            Paragraph(Text("S is any finite set of actual primes such that p^2 >= 2x and p+1 <= x. "
                + "The endpoints are weak and S may be empty. Write B(S) = sum_S [1/p - log(1+1/p)] "
                + "and C(S) = sum_S 1/[2p(p+1)]. Put U = T_x union n.primeFactors, "
                + "A = sum_S [u_p(1) - u_p(n.factorization p)], and "
                + "K = sum_(U minus S) [H_p(v_p) - u_p(n.factorization p)]. "
                + "Primes of n beyond the reference support remain in K.")),
            Describe.Lean(DescribeId.Create("actual-reference-full-pressure-gap-decomposition"),
                DeclarationHandle.Create(Prefix + "actual_reference_gap_decomposition"),
                H("Exact gap with both remainder sums"),
                StatementSource.FromAuthor(DecompositionFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The finite reference maximum supplies H_p(v_p) >= u_p(a) for every exponent. "
                        + "On S the inclusive reference exponent is one. The actual first marginal is strictly "
                        + "above lambda_x and the second strictly below it, even at the weak endpoints. "
                        + "The original generic strict-threshold maximum in GoldenResource5040PriceInterval "
                        + "therefore gives u_p(a) <= u_p(1), without assuming p divides n.")),
                    Paragraph(Text("The original local_eq_layer_sum in GoldenResourceSupremum is exposed in place "
                        + "and identifies u_p(1) = log(1+1/p) - lambda_x log p. "
                        + "The existing golden_resource_objective_sum_on factors the actual objective on U. "
                        + "Subtracting the two exact finite sums and splitting S from its complement yields "
                        + "F-J = B+A+K. Both remainder sums are nonnegative. "
                        + "PrefixDeficitKernel.result at exponent one and ratio 1/p supplies C <= B inside this live composition.")),
                    Paragraph(Text("At n=1 all actual exponents are zero; A retains u_p(1)-u_p(0). "
                        + "An empty mask leaves the full nonnegative complement. At p^k=x the last reference "
                        + "gain is zero, so omitting or including that layer gives the same F."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-unrestricted-reserve-prime-mask-consumer"),
                DeclarationHandle.Create(Prefix + "actual_reserve_prime_mask"),
                H("The same actual reserve and integer defect"),
                StatementSource.FromAuthor(ReserveFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("GoldenFutureExtensionMaximum.golden_future_extension_maximum_attained "
                        + "at base one and positive lambda_x supplies an actual integer attaining the unrestricted "
                        + "greatest objective value. Apply the preceding uniform inequality to that integer to obtain "
                        + "Res >= B >= C. The greatest-element property also yields d_x(n) >= 0 for every positive n. "
                        + "The exact sigma identity identifies J_x(n). Its gap is Res+d and is bounded below by B. "
                        + "No least/largest optimizer choice is substituted. All actual equality-price choices have "
                        + "the same pressure value; the existing supremum owner supplies that invariance.")),
                    Paragraph(Text("This implements the original section 87 finite reserve mechanism. "
                        + "Original section 93.2 already gives the stronger two-candidate producer on sqrt(x)<p<=x-1: "
                        + "the local reserve is min(1/p-log(1+1/p), "
                        + "1/p-log(1+1/p+1/p^2)+lambda_x log p), with actual exponent one or two and all ties. "
                        + "Its prose bound 0<=Res-B2<=5 x^(-2/3)+2/x holds for every real x>1. "
                        + "Under unconditional PNT its scaled reserve tends to 2(sqrt(2)-1). "
                        + "Those stronger ordinary results are reused context, with no new finite start or Lean acceptance claimed here.")),
                    Paragraph(Text("For the full Robin target at E=log n the signed identity remains "
                        + "Delta(n)=Ipsi(E)+Res(E)+d_E(n). A reserve lower bound does not control the signed Ipsi term. "
                        + "The existing section 491 calculation gives Ipsi(log5041)+Res(log5041)<-1/200, "
                        + "using the actual candidate integer 2520 only to lower-bound M; it does not assert an optimizer. "
                        + "Deleting d globally would therefore lose a necessary contribution. "
                        + "A faithful same-source signed estimate retaining d for all n>5040 remains unpaid. "
                        + "The full RH/Robin/5040 goal is active and unproved. The later Chebyshev/dyadic "
                        + "budget and unbounded PNT formalization are separate from this finite step."))), DescribeRole.Theorem))));

    private static Formula Hypotheses() => Seq(F.Id("x"), Gt, D(1), Land,
        Call("PrimeMask", F.Id("x"), F.Id("S")), Land, F.Id("n"), Ge, D(1));

    private static Formula Quantifiers() => Seq(Forall, Sp, F.Id("x"), InMacro,
        Mathbb, Grp(F.Id("R")), Comma, F.Id("S"), InMacro, Call("Finset", F.Id("N")),
        Comma, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma);

    private static Formula DecompositionFormula() => Disp(Seq(Quantifiers(), Hypotheses(), Rightarrow,
        Grp(Seq(Call("F", F.Id("x")), Minus, Call("J", F.Id("x"), F.Id("n")), Eq,
            Call("B", F.Id("S")), Plus, Call("A", F.Id("x"), F.Id("S"), F.Id("n")), Plus,
            Call("K", F.Id("x"), F.Id("S"), F.Id("n")))), Land,
        D(0), Le, Call("A", F.Id("x"), F.Id("S"), F.Id("n")), Land,
        D(0), Le, Call("K", F.Id("x"), F.Id("S"), F.Id("n")), Land,
        Call("C", F.Id("S")), Le, Call("B", F.Id("S"))));

    private static Formula ReserveFormula() => Disp(Seq(Quantifiers(), Hypotheses(), Rightarrow,
        Call("C", F.Id("S")), Le, Call("B", F.Id("S")), Le, Call("Res", F.Id("x")), Land,
        D(0), Le, Call("d", F.Id("x"), F.Id("n")), Land,
        Call("F", F.Id("x")), Minus, Call("J", F.Id("x"), F.Id("n")), Eq,
        Call("Res", F.Id("x")), Plus, Call("d", F.Id("x"), F.Id("n")), Land,
        Call("B", F.Id("S")), Le, Call("Res", F.Id("x")), Plus, Call("d", F.Id("x"), F.Id("n"))));

    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
}
