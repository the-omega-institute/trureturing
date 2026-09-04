using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms;

internal sealed class PrimaryPseudoperfectPortsDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix = "D5/S3/PrimeForms/PrimaryPseudoperfectPorts.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Primary pseudoperfect numbers admit exact reciprocal and prime-extension laws.",
        H("Primary Pseudoperfect Reciprocal and Extension Laws"),
        Blocks(
            Paragraph(Text(
                "Write d(n) for the sum of n divided by p over the distinct prime divisors p "
                    + "of n, and R(n) for the corresponding sum of rational reciprocals 1/p.")),
            Describe.Lean(
                DescribeId.Create("squarefree-derivative-rational-cast"),
                DeclarationHandle.Create(DeclarationPrefix + "squarefreeDeriv_cast"),
                H("The quotient sum casts to the reciprocal-prime sum"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("d", N), Sp, Eq, Sp, N, Sp, Call("R", N), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every prime in primeFactors n divides n and is nonzero. Mathlib's "
                        + "Nat.cast_div therefore converts each natural quotient n / p to the "
                        + "rational quotient, and distributivity factors out n."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reciprocal-sum-equals-one-iff"),
                DeclarationHandle.Create(DeclarationPrefix + "reciprocal_sum_eq_one_iff"),
                H("The reciprocal and integral identities are equivalent"),
                StatementSource.FromAuthor(Disp(Seq(
                    N, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
                    new Formula.Fraction(D(1), N), Sp, Plus, Sp, Call("R", N), Sp,
                    Eq, Sp, D(1), Sp, Leftrightarrow, Sp,
                    N, Sp, Eq, Sp, D(1), Sp, Plus, Sp, Call("d", N), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Multiplication by the nonzero rational n and the cast identity turn one "
                        + "equation into the other. The explicit nonzero premise excludes the "
                        + "totalized division value at n = 0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("primary-pseudoperfect-reciprocal-characterization"),
                DeclarationHandle.Create(DeclarationPrefix + "isPPN_iff_reciprocal_sum"),
                H("Primary pseudoperfectness is the reciprocal identity"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("IsPPN", N), Sp, Leftrightarrow, Sp,
                    Call("Squarefree", N), Sp, Land, Sp, D(1), Sp, Lt, Sp, N, Sp, Land, Sp,
                    new Formula.Fraction(D(1), N), Sp, Plus, Sp, Call("R", N), Sp,
                    Eq, Sp, D(1), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The strict lower bound n > 1 supplies n != 0 in both directions, so the "
                        + "reciprocal theorem applies without a hidden degenerate case."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("squarefree-derivative-prime-extension"),
                DeclarationHandle.Create(DeclarationPrefix + "squarefreeDeriv_mul_prime"),
                H("A new prime gives a one-step quotient expansion"),
                StatementSource.FromAuthor(Disp(Seq(
                    K, Sp, Neq, Sp, D(0), Sp, Land, Sp, Call("Prime", P), Sp, Land, Sp,
                    Neg, Call("Divides", P, K), Sp, Rightarrow, Sp,
                    Call("d", Seq(K, P)), Sp, Eq, Sp,
                    P, Call("d", K), Sp, Plus, Sp, K, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The prime-factor set of Kp is the disjoint union of the factors of K and "
                        + "the new prime p. Old quotients scale by p, while the new quotient is K."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("squarefree-derivative-two-prime-extension"),
                DeclarationHandle.Create(DeclarationPrefix + "squarefreeDeriv_mul_two_primes"),
                H("Two new primes give the iterated quotient expansion"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("FreshDistinctPrimes", K, P, Q), Sp, Rightarrow, Sp,
                    Call("d", Seq(K, P, Q)), Sp, Eq, Sp,
                    Q, Grp(P, Call("d", K), Sp, Plus, Sp, K), Sp, Plus, Sp, K, P, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Applying the one-prime expansion first to p and then to q gives the formula; "
                        + "distinctness ensures q is still new after adjoining p."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("primary-pseudoperfect-successor-prime-extension"),
                DeclarationHandle.Create(DeclarationPrefix + "isPPN_mul_succ"),
                H("A prime successor preserves primary pseudoperfectness"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("IsPPN", K), Sp, Land, Sp, Call("Prime", Grp(K, Sp, Plus, Sp, D(1))),
                    Sp, Rightarrow, Sp,
                    Call("IsPPN", Seq(K, Grp(K, Sp, Plus, Sp, D(1)))), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A number and its successor are coprime. The prime-extension formula and "
                        + "the identity K = 1 + d(K) then close the new quotient identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("primary-pseudoperfect-two-prime-factor-equation"),
                DeclarationHandle.Create(DeclarationPrefix + "isPPN_mul_two_primes_iff"),
                H("The two-prime extension is an integer factor equation"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("IsPPN", K), Sp, Land, Sp, Call("FreshDistinctPrimes", K, P, Q),
                    Sp, Rightarrow, Sp, Open,
                    Call("IsPPN", Seq(K, P, Q)), Sp, Leftrightarrow, Sp,
                    Grp(P, Sp, Minus, Sp, K), Grp(Q, Sp, Minus, Sp, K), Sp, Eq, Sp,
                    Call("sq", K), Sp, Plus, Sp, D(1), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The equation is stated over the integers, so neither subtraction is "
                        + "silently truncated. Expanding both sides is equivalent to the new "
                        + "primary-pseudoperfect quotient identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("primary-pseudoperfect-numerical-chain"),
                DeclarationHandle.Create(DeclarationPrefix + "primary_pseudoperfect_numerical_chain"),
                H("The first five numerical witnesses"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("IsPPN", D(2)), Sp, Land, Sp, Call("IsPPN", D(6)), Sp, Land, Sp,
                    Call("IsPPN", D(4, 2)), Sp, Land, Sp, Call("IsPPN", D(1, 8, 0, 6)),
                    Sp, Land, Sp, Call("IsPPN", D(4, 7, 0, 5, 8)), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The first four terms follow by repeated prime-successor extension. The last "
                        + "uses the squarefree factorization 2 * 3 * 11 * 23 * 31 and computes "
                        + "its quotient sum as 47057."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula N => F.Id("n");
    private static Formula K => F.Id("K");
    private static Formula P => F.Id("p");
    private static Formula Q => F.Id("q");
}
