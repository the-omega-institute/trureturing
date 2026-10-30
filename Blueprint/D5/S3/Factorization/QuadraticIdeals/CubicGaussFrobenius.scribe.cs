using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class CubicGaussFrobeniusDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/QuadraticIdeals/CubicGaussFrobenius.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gauss sums and two Frobenius comparisons give cubic reciprocity at distinct rational prime residue cardinalities.",
        H("Cubic Gauss Sums, Frobenius, and Primary Reciprocity"),
        Blocks(
            Paragraph(Text(
                "Write E = Z[omega], with omega the standard primitive cube root of unity in the Eisenstein order. "
                + "For a maximal ideal P with finite residue field of cardinality congruent to 1 modulo 3 and with 3 not in P, "
                + "chi_P is the existing Euler cubic residue character on E/P, extended by zero at zero. Its nonzero values "
                + "are the unique elements of {1, omega, omega^2} reducing to x^((card(E/P)-1)/3). An expression chi_P(a) "
                + "for a in E means evaluation at a mod P. A primary generator pi means exactly (pi) = P and 3 divides pi-1.")),
            Paragraph(Text(
                "For the arithmetic comparison and reciprocity endpoints below, p and q are distinct rational primes, both "
                + "congruent to 1 modulo 3. The maximal ideals P and Q have residue cardinalities exactly p and q. Thus their "
                + "residue characteristics are p and q. Prime cardinality is a hypothesis of these endpoints; it is not replaced "
                + "by a prime-power cardinality. The companion CubicJacobiNormalization supplies J(chi_P,chi_P) = -pi and "
                + "Norm(pi) = p from the stated generator and primary assumptions, rather than taking either identity as a premise.")),
            Describe.Lean(
                DescribeId.Create("cubic-gauss-euler-comparison"),
                DeclarationHandle.Create(Prefix + "cubic_gauss_euler_comparison"),
                H("The finite-sum convention fixes the inverse character value"),
                StatementSource.FromAuthor(Disp(F.Seq(
                    FiniteSumParameters(),
                    Call("inv", Call("chi", Cast(F.Id("q"), F.Id("F")))), Eq,
                    Call("pow", Call("mul", Cast(Call("card", F.Id("F")), F.Id("K")),
                        Call("jacobiSum", F.Id("chi"), F.Id("chi"))), Exponent())))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Here F is a finite field, K is a field of prime characteristic q, chi : MulChar F K has exact order three, "
                    + "and psi : AddChar F K is primitive. In addition to q congruent to 1 modulo 3, the cast of q in F must be "
                    + "a unit and the cast of card(F) in K must be nonzero. These are the actual parameters of this reusable "
                    + "finite-sum statement. With Mathlib's convention G = sum_x chi(x) psi(x), gaussSum_frob, "
                    + "AddChar.pow_mulShift, and gaussSum_mulShift_eq give G^q = chi(q)^(-1) G. The character is not replaced "
                    + "by its inverse, and the additive character is not replaced by psi^(-1). The exact cubic Gauss identity "
                    + "is G^3 = card(F) J(chi,chi); its cardinality factor is not inverted. Primitivity, nontriviality of chi, "
                    + "and the nonzero cardinality cast give G nonzero. Cancelling G and using q-1 = 3((q-1)/3) yields the "
                    + "displayed inverse-character comparison. This lemma alone is not a prime-power reciprocity statement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cubic-roots-reduction-injective"),
                DeclarationHandle.Create(Prefix + "cubic_roots_injective"),
                H("Only the three cubic roots are transported injectively"),
                StatementSource.FromAuthor(Disp(F.Seq(
                    Forall, Sp, F.Id("K"), Comma, Sp, Call("commRing", F.Id("K")), Comma, Sp,
                    Call("isDomain", F.Id("K")), Comma, Sp,
                    Forall, Sp, F.Id("f"), Colon, Sp, Call("ringHom", F.Id("E"), F.Id("K")), Comma, Sp,
                    Call("neq", Call("f", D(3)), D(0)), Comma, Sp,
                    Forall, Sp, F.Id("z"), Comma, Sp, F.Id("zPrime"), Colon, Sp, F.Id("E"), Comma, Sp,
                    Call("IsCubicRoot", F.Id("z")), Comma, Sp,
                    Call("IsCubicRoot", F.Id("zPrime")), Comma, Sp,
                    Call("f", F.Id("z")), Eq, Call("f", F.Id("zPrime")),
                    Sp, Implies, Sp, F.Id("z"), Eq, F.Id("zPrime")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "IsCubicRoot(z) means the literal disjunction z = 1 or z = omega or z = omega^2. "
                    + "For a ring homomorphism f : E -> K into a commutative domain, the hypothesis f(3) nonzero keeps these "
                    + "three images distinct. The proof uses omega^2+omega+1 = 0 and "
                    + "(1-omega)(1-omega^2) = 3. No global injectivity of f is asserted. In the arithmetic application, "
                    + "f factors through E/Q and has a kernel; only its restriction to these three roots is used to lift "
                    + "equalities. The field inclusion E/Q -> K is a different map and is injective."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cubic-gauss-primary-scalar"),
                DeclarationHandle.Create(Prefix + "cubic_gauss_primary_scalar"),
                H("Primary Jacobi normalization determines the Gauss scalar"),
                StatementSource.FromAuthor(Disp(F.Seq(
                    PrimaryScalarParameters(),
                    Call("inv", Call("f", Chi("P", Cast(F.Id("q"), F.Id("E"))))), Eq,
                    Call("pow", Call("f", Call("mul", F.Seq(Minus, Cast(F.Id("p"), F.Id("E"))),
                        F.Id("pi"))), Exponent())))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The scalar statement takes P maximal with finite residue field of cardinality p, distinct rational "
                    + "primes p and q both congruent to 1 modulo 3, and a specified primary generator pi of P. It also takes "
                    + "a field K of characteristic q, a ring homomorphism f : E -> K with f(3) nonzero, and a primitive "
                    + "additive character psi : AddChar (E/P) K. These are explicit parameters at this intermediate endpoint. "
                    + "Restricted cubic-root transport preserves the exact order three of the transported P-character. "
                    + "Distinctness p != q gives the nonzero casts required in the finite-sum lemma. Reuse of the companion "
                    + "Jacobi normalization replaces J_P by -pi, so the cube scalar becomes -p pi. Consequently the left side "
                    + "is f(chi_P(q))^(-1), with the inverse retained. No Gauss cube identity, Frobenius eigenvalue, "
                    + "or Jacobi value is added as an assumption."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cubic-residue-prime-comparison"),
                DeclarationHandle.Create(Prefix + "cubic_residue_prime_comparison"),
                H("The asymmetric comparison for the actual residue characters"),
                StatementSource.FromAuthor(Disp(F.Seq(
                    ArithmeticParameters(), PrimaryGenerator("pi", "P"), Sp, Implies, Sp,
                    Chi("P", Cast(F.Id("q"), F.Id("E"))), Eq,
                    Call("mul", Chi("Q", F.Id("pi")),
                        Call("pow", Chi("Q", Call("star", F.Id("pi"))), D(2)))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "This arithmetic endpoint assumes P and Q maximal, both quotients finite, card(E/P) = p, "
                        + "card(E/Q) = q, p and q rational primes congruent to 1 modulo 3, p != q, and pi a primary "
                        + "generator of P. It has no supplied extension field, map f, or additive character as an extra "
                        + "hypothesis. The proof constructs a primitive additive character of E/P in a cyclotomic extension "
                        + "of E/Q. Its characteristic is q. The reduction f : E -> K factors through Q, and f(3) is nonzero.")),
                    Paragraph(Text(
                        "Normalization derives Norm(pi) = p, hence p = pi star(pi). Since p is nonzero modulo Q, "
                        + "both pi and star(pi) are nonzero there; q is likewise nonzero modulo P. Put a = chi_P(q), "
                        + "b = chi_Q(pi), c = chi_Q(star(pi)), and d = chi_Q(-p pi). Euler reduction at Q turns the "
                        + "scalar identity into f(a)^(-1) = f(d). The cubic-root restriction lifts the resulting product "
                        + "to a d = 1 in E. Multiplicativity, p = pi star(pi), and chi_Q(-1) = 1 give d = b^2 c. "
                        + "The cubic-root relations then give a = b c^2, exactly the displayed direction. The inverse "
                        + "in the Gauss comparison is therefore essential to the final orientation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cubic-primary-reciprocity"),
                DeclarationHandle.Create(Prefix + "cubic_reciprocity_primary"),
                H("Two derived Gauss comparisons give primary cubic reciprocity"),
                StatementSource.FromAuthor(Disp(F.Seq(
                    ArithmeticParameters(), PrimaryGenerator("pi", "P"), Comma, Sp,
                    PrimaryGenerator("rho", "Q"), Sp, Implies, Sp,
                    Chi("Q", F.Id("pi")), Eq, Chi("P", F.Id("rho"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For the final endpoint, pi and rho are specified elements of E satisfying (pi) = P, "
                        + "(rho) = Q, 3 divides pi-1, and 3 divides rho-1, in addition to all the prime-cardinality "
                        + "and distinctness assumptions above. Norm(pi) = p and Norm(rho) = q are derived from "
                        + "CubicJacobiNormalization. No reciprocity identity, Jacobi value, norm identity, or choice "
                        + "between conjugate ideals is assumed by the final statement.")),
                    Paragraph(Text(
                        "Set A = chi_Q(pi), B = chi_Q(star(pi)), C = chi_P(rho), and D = chi_P(star(rho)). "
                        + "The first arithmetic comparison and q = rho star(rho) give C D = A B^2. Applying the same "
                        + "comparison with P,p,pi and Q,q,rho exchanged gives A B = C D^2. These two comparisons are "
                        + "proved before invoking cubic_reciprocity_algebra; they are not arithmetic premises. The "
                        + "algebra helper needs only A^3 = B^3 = 1 and those two comparisons. It obtains B D = 1 "
                        + "and then A = C, without a global injectivity premise for reduction.")),
                    Paragraph(Text(
                        "This is classical cubic reciprocity for distinct rational prime residue cardinalities. "
                        + "The convention and classical context are recorded in Dunn and Radziwill, "
                        + "arXiv:2109.07463v3, equations (1.4)-(1.5). The proof combines the Euler selector, "
                        + "the companion Jacobi normalization, and Mathlib's exact Gauss, Jacobi, and additive-character "
                        + "identities.")),
                    Paragraph(Text(
                        "Scope still outside this arithmetic endpoint: general prime-power residue cardinalities, "
                        + "including the cardinality-four case covered by the companion normalization; equal residue "
                        + "characteristics; the two conjugate primes over one rational prime; ramified primes at three; "
                        + "and a reciprocity statement for arbitrary composite ideals. The present final theorem does "
                        + "not assert those extensions. The finite-sum lemmas and the normalization lemma retain "
                        + "their own separately stated domains."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Cast(Formula value, Formula target) => Call("cast", value, target);
    private static Formula Quotient(string ideal) => Call("quotient", F.Id("E"), F.Id(ideal));
    private static Formula Chi(string ideal, Formula value) =>
        Call("chi", F.Id(ideal), Call("modIdeal", value, F.Id(ideal)));
    private static Formula Exponent() => Call("natDiv", F.Seq(F.Id("q"), Minus, D(1)), D(3));

    private static Formula PrimeParameters() => F.Seq(
        Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp, F.Id("Nat"), Comma, Sp,
        Call("prime", F.Id("p")), Comma, Sp, Call("prime", F.Id("q")), Comma, Sp,
        Call("mod", F.Id("p"), D(3)), Eq, D(1), Comma, Sp,
        Call("mod", F.Id("q"), D(3)), Eq, D(1), Comma, Sp,
        Call("neq", F.Id("p"), F.Id("q")), Comma, Sp);

    private static Formula ArithmeticParameters() => F.Seq(
        Forall, Sp, F.Id("P"), Comma, Sp, F.Id("Q"), Colon, Sp, Call("Ideal", F.Id("E")), Comma, Sp,
        Call("maximal", F.Id("P")), Comma, Sp, Call("maximal", F.Id("Q")), Comma, Sp,
        Call("finite", Quotient("P")), Comma, Sp, Call("finite", Quotient("Q")), Comma, Sp,
        PrimeParameters(),
        Call("card", Quotient("P")), Eq, F.Id("p"), Comma, Sp,
        Call("card", Quotient("Q")), Eq, F.Id("q"), Comma, Sp);

    private static Formula PrimaryGenerator(string element, string ideal) => F.Seq(
        Forall, Sp, F.Id(element), Colon, Sp, F.Id("E"), Comma, Sp,
        Call("spanSingleton", F.Id(element)), Eq, F.Id(ideal), Comma, Sp,
        Call("divides", Cast(D(3), F.Id("E")), F.Seq(F.Id(element), Minus, D(1))));

    private static Formula FiniteSumParameters() => F.Seq(
        Forall, Sp, F.Id("F"), Comma, Sp, F.Id("K"), Comma, Sp,
        Call("field", F.Id("F")), Comma, Sp, Call("finite", F.Id("F")), Comma, Sp,
        Call("field", F.Id("K")), Comma, Sp,
        Forall, Sp, F.Id("chi"), Colon, Sp, Call("MulChar", F.Id("F"), F.Id("K")), Comma, Sp,
        Call("orderOf", F.Id("chi")), Eq, D(3), Comma, Sp,
        Forall, Sp, F.Id("psi"), Colon, Sp, Call("AddChar", F.Id("F"), F.Id("K")), Comma, Sp,
        Call("primitive", F.Id("psi")), Comma, Sp,
        Forall, Sp, F.Id("q"), Colon, Sp, F.Id("Nat"), Comma, Sp,
        Call("prime", F.Id("q")), Comma, Sp, Call("CharP", F.Id("K"), F.Id("q")), Comma, Sp,
        Call("mod", F.Id("q"), D(3)), Eq, D(1), Comma, Sp,
        Call("isUnit", Cast(F.Id("q"), F.Id("F"))), Comma, Sp,
        Call("neq", Cast(Call("card", F.Id("F")), F.Id("K")), D(0)),
        Sp, Implies, Sp);

    private static Formula PrimaryScalarParameters() => F.Seq(
        Forall, Sp, F.Id("P"), Colon, Sp, Call("Ideal", F.Id("E")), Comma, Sp,
        Call("maximal", F.Id("P")), Comma, Sp, Call("finite", Quotient("P")), Comma, Sp,
        PrimeParameters(), Call("card", Quotient("P")), Eq, F.Id("p"), Comma, Sp,
        PrimaryGenerator("pi", "P"), Comma, Sp,
        Forall, Sp, F.Id("K"), Comma, Sp, Call("field", F.Id("K")), Comma, Sp,
        Call("CharP", F.Id("K"), F.Id("q")), Comma, Sp,
        Forall, Sp, F.Id("f"), Colon, Sp, Call("ringHom", F.Id("E"), F.Id("K")), Comma, Sp,
        Call("neq", Call("f", D(3)), D(0)), Comma, Sp,
        Forall, Sp, F.Id("psi"), Colon, Sp, Call("AddChar", Quotient("P"), F.Id("K")), Comma, Sp,
        Call("primitive", F.Id("psi")), Sp, Implies, Sp);
}
