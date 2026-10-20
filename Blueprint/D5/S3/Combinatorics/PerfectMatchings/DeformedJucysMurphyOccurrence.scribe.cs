using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PerfectMatchings;

internal sealed class DeformedJucysMurphyOccurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyOccurrence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal differential operator and native matching operator use exactly one occurrence coefficient on every partition.",
        H("The Common Coefficient in Coulter–Do Conjecture 5.8"),
        Blocks(
            Paragraph(Text("Work in the infinite polynomial algebra on the positive power sums. "
                + "For a partition rho, p(rho) has the literal part multiplicities as exponents. "
                + "B(b,rho,sigma) denotes the coefficient of p(sigma) in the literal ordered differential "
                + "operator D_b(p(rho)); R(b,rho,sigma) denotes the canonical native rowCoefficient. "
                + "The proof first extends the exponent encoding to arbitrary positive residual multisets, "
                + "including the empty multiset. A derivative is a sum over erased occurrences. Two "
                + "derivatives erase distinct occurrences in order, retaining repeated and equal parts.")),
            Describe.Lean(DescribeId.Create("literal-occurrence-coefficient"),
                DeclarationHandle.Create(Prefix + "operatorCoefficient_eq_rowCoefficient"),
                H("Literal Coefficients Equal Canonical Native Occurrences"),
                StatementSource.FromAuthor(Disp(All("K", V("CharZeroField"), All("b", V("K"),
                    OverPartitions(Equal(Call("B", V("b"), V("rho"), V("sigma")),
                        Call("R", V("b"), V("rho"), V("sigma")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For cuts, the two derivative indices correspond bijectively to "
                    + "the positive ordered displacement d with 0<d<r. Both equal halves and complementary "
                    + "cuts remain. For joins, the second occurrence belongs to rho with the first occurrence "
                    + "erased. The diagonal identity is choose(r,2)=r(r-1)/2. Coefficient extraction separates "
                    + "distinct partitions by exponent injectivity. These arguments include zero coefficients, "
                    + "singleton ranges and empty residual monomials, without a correspondence premise."))),
                DescribeRole.Theorem),
            Paragraph(Text("Now K=RatFunc Complex, beta=X, alpha=1+X and "
                + "A(rho)=alpha^(number of parts)*product_r r^(multiplicity r)*(multiplicity r)!. "
                + "Every A(rho) is nonzero. Define c_lambda(mu)=R(beta,mu,lambda).")),
            Paragraph(Text("The coefficient equality also transports the algebraic detailed balance "
                + "to the native coefficient: A(sigma)*R(beta,rho,sigma) equals "
                + "A(rho)*R(beta,sigma,rho), including unrelated zero branches. "
                + "The live C2 proof applies the algebraic normalized expansion directly through "
                + "the coefficient equality; no separate transported balance theorem is needed.")),
            Describe.Lean(DescribeId.Create("same-c-c2"),
                DeclarationHandle.Create(Prefix + "same_coefficient_C2"),
                H("C2 with Exactly the C1 Coefficient"),
                StatementSource.FromAuthor(Disp(All("k", V("Nat"),
                    All("lambda", Call("Partition", V("k")), Equal(
                        Seq(Sum, Underscore, Grp(V("mu"), InMacro, Call("Partition", V("k"))),
                            Grp(Mul(Fraction(Call("c", V("lambda"), V("mu")), Call("A", V("mu"))),
                                Call("p", V("mu"))))),
                        Call("D", Mul(Fraction(D(1), Call("A", V("lambda"))), Call("p", V("lambda"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Divide balance by the two nonzero normalizations and use the "
                    + "literal operator's homogeneous partition expansion. The coefficient remains "
                    + "R(beta,mu,lambda), in the native C1 orientation."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-joint-consumer"),
                DeclarationHandle.Create(Prefix + "conjecture58"),
                H("The Original Joint Native and Polynomial Statement"),
                StatementSource.FromAuthor(Disp(All("k", Call("PositiveNat"),
                    All("lambda", Call("Partition", V("k")),
                        Call("UniqueCommonCoefficient", V("k"), V("lambda")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("UniqueCommonCoefficient means that there is exactly one function "
                    + "c from all partitions of k to K for which S_beta(indicator lambda)(p)=c(ct(p)) "
                    + "for every actual native matching p, and the displayed C2 identity holds with "
                    + "c(mu) in its numerator. Existence uses native_C1 and same_coefficient_C2 with "
                    + "c(mu)=R(beta,mu,lambda). Uniqueness uses matching_realization at each partition "
                    + "mu and evaluates the native function equality at that actual matching. Thus no "
                    + "partition is silently excluded or assigned an unconstrained coefficient."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("coulter-do-2025-conjecture-5-8"), ResolutionKind.Proved)))));

    private static Formula V(string s) => F.Id(s);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula OverPartitions(Formula body) => All("k", V("Nat"),
        All("rho", Call("Partition", V("k")), All("sigma", Call("Partition", V("k")), body)));
    private static Formula Mul(Formula a, Formula b) => Seq(Grp(a), Cdot, Grp(b));
    private static Formula Fraction(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
}
