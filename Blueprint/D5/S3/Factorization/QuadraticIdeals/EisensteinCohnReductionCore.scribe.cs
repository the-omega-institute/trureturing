using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class EisensteinCohnReductionCoreDocument : IScribeDocumentDefinition
{
    private static Formula I(string s) => F.Id(s);
    private static Formula.BoundVariable B(string s, Formula t) => new(FormulaIdentifier.Create(s), t);
    private static Formula All(Formula f, params Formula.BoundVariable[] v) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. v], f);
    private static DocumentBlock Helper(string n, Formula f, string p) => Describe.Lean(
        DescribeId.Create(n.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(
            "D5/S3/Factorization/QuadraticIdeals/EisensteinCohnReductionCore." + n), H(n),
        StatementSource.FromAuthor(Disp(f)), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(p))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The square-plus-three equation has no integer solution with x at least two and exponent at least two.",
        H("The Eisenstein Reduction for All Integer Powers"),
        Blocks(
            Helper("norm_unit_one",
                All(Equal(Call("norm", Call("unitValue", I("u"))), Num(1)),
                    B("u", Call("Units", I("EisensteinOrder")))),
                "Every integral Eisenstein unit has norm one. This existing owner proof is reused "
                + "unchanged and is also consumed by ResetIntegralUnits after the imaginary "
                + "coefficient vanishes, forcing the real coefficient to be plus or minus one."),
            Helper("unit_modTwo",
                All(new Formula.Logic(Equal(Call("modTwo", Call("unitValue", I("u"))), Num(1)),
                    FormulaLogicOperator.Implies, Equal(Call("im", Call("unitValue", I("u"))), Num(0))),
                    B("u", Call("Units", I("EisensteinOrder")))),
                "EisensteinOrder is QuadraticAlgebra Int (-1) (-1); the public ETwo abbreviation "
                + "is the same algebra over ZMod 2. modTwo literally reduces both coefficients. "
                + "The existing unit_modTwo gives imaginary coefficient zero for a unit reducing "
                + "to one. It does not alone conclude plus or minus one. ResetIntegralUnits "
                + "consumes it together with norm_unit_one at this owner."),
            Describe.Lean(
                DescribeId.Create("int-sq-add-three-not-pow"),
                DeclarationHandle.Create("D5/S3/Factorization/QuadraticIdeals/EisensteinCohnReductionCore.int_sq_add_three_not_pow"),
                H("Square plus three is not a nontrivial integer power"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Sp,
                    Forall, Sp, F.Id("e"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    D(2), Sp, Le, Sp, F.Id("x"), Sp, Rightarrow, Sp,
                    D(2), Sp, Le, Sp, F.Id("e"), Sp, Rightarrow, Sp,
                    new Formula.Not(Seq(new Formula.Power(F.Id("x"), D(2)), Sp, Plus, Sp, D(3), Sp, Eq, Sp,
                        new Formula.Power(F.Id("y"), F.Id("e"))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Factorization/cohn1993squareplusthree")),
                Blocks(
                    Paragraph(Text(
                        "The base y ranges over all integers, and the natural exponent e has no upper bound. "
                        + "Cohn's classical positive-base argument supplies the three-adic obstruction; the formal reduction here also handles the square case and retains the signed base throughout.")),
                    Paragraph(Text(
                        "Suppose x squared plus three equals y to the power e. If e is even, write e=2k. "
                        + "Then the square of the integer absolute value of y to the power k is strictly between x squared and (x+1) squared, since x is at least two. "
                        + "For odd e, choose a prime divisor q and set Y=y^(e/q). The equation becomes x squared plus three equals Y to the power q, with q odd. "
                        + "If x were odd, Y would be even and reduction modulo eight would give a contradiction. If three divided x, reduction modulo three would force three to divide Y, and reduction modulo nine would again contradict the equation. "
                        + "Thus x is even, three does not divide x, and x squared plus three is coprime to twelve.")),
                    Paragraph(Text(
                        "Work in the Eisenstein integer ring with omega squared plus omega plus one equal to zero. "
                        + "Set alpha=(x+1)+2 omega and beta equal to its conjugate. Their product is x squared plus three, and minus the square of their difference is twelve. "
                        + "The integer Bezout identity for the norm and twelve therefore gives an explicit Bezout identity for alpha and beta. "
                        + "The existing cyclotomic equivalence transports the principal ideal ring structure, so Mathlib's coprime power extraction produces gamma to the power q times a unit epsilon equal to alpha.")),
                    Paragraph(Text("The ring and its cyclotomic equivalence are supplied by "),
                        Ref("D5/S3/Factorization/QuadraticIdeals/EisensteinOddQuotient"),
                        Text(" and "), Ref("D5/S3/Factorization/QuadraticIdeals/EisensteinCyclotomicBridge"), Text(".")),
                    Paragraph(Text(
                        "Reduction modulo two sends alpha to one. For an element z of this quadratic algebra over the two-element field, z cubed is the scalar norm of z. "
                        + "When q=3 this forces epsilon to reduce to one. Its norm is one, so its imaginary coordinate is zero; the imaginary coordinate of gamma cubed times epsilon is then divisible by three, contradicting the coordinate two of alpha. "
                        + "For q different from three, q is coprime to six. The existing cyclotomic classification of the six units allows epsilon to be absorbed into a qth root delta. "
                        + "Modulo two, delta has both qth power and cube equal to one. Coprimality forces delta itself to reduce to one, so its imaginary coordinate is even.")),
                    Paragraph(Text(
                        "The injective map from the integral suborder sends a+b sqrt(-3) to (a+b)+2b omega. "
                        + "The even imaginary coordinate pulls delta back through this map and gives an actual identity (a+b sqrt(-3))^q=x+sqrt(-3). "
                        + "Induction shows that b divides the imaginary coefficient of every power, hence b divides one and is plus or minus one. "
                        + "Taking norms and reducing modulo four and three shows that a is even and three does not divide a.")),
                    Paragraph(Text(
                        "Put xi=a squared minus one and m=(q-1)/2. The owner polynomial is P_q(T), the sum from k=0 to m of binom(q,2k+1)(-3)^k(1+T)^(m-k). "
                        + "Its existing polynomial identification and evaluation hom give P_q(xi) as the imaginary coordinate of (a+sqrt(-3))^q. "
                        + "The sign b=plus or minus one yields P_q(xi)=plus or minus one. Modulo four, only the k=m term survives and has value one, forcing P_q(xi)=1. "
                        + "Modulo three, only k=0 survives and has value q, forcing q congruent to one modulo three. "
                        + "Together with odd q at least five, this gives q at least seven and q congruent to one modulo six; three also divides xi. "
                        + "The uniform Cohn obstruction now contradicts P_q(xi)=1.")),
                    Paragraph(Text("The polynomial identity, evaluation hom, and final obstruction are reused from "),
                        Ref("D5/S3/Arith/Congruence/CohnUniformThreeAdic"),
                        Text(". The reduction assumes neither an Eisenstein root nor coprimality: both are derived from the original equation.")),
                    Paragraph(Text("The same exclusion applies to every signed integer x when e is at least three. Replace x by its absolute value when |x| is at least two. For x=-1,0,1 the left side is four or three; an integer base of absolute value at least two has e-th power of absolute value at least eight, while bases of absolute value zero or one give zero or one. Thus these small values give no additional solutions.")),
                    Paragraph(Text("For the actual golden blocks put r_j=3^(j+1), B_j=natAbs(L_(3^j)^2+3), T_j equal to its prime support, and h_p=v_p(F_(p-(5/p))) at the original signed Fibonacci index. The cubic block product gives L_(3^j)>=4 for j>=1. GoldenCubicBlockRanks.cubic_block_b_prime_rank and FibonacciPrimeToIndexValuation.fibonacci_original_rank_valuation identify every exponent of B_j with this h_p. In particular the support is nonempty and every depth is positive. If a fixed e>=2 divided all these depths, Y=product(p in T_j,p^(h_p/e)) would satisfy B_j=Y^e, contrary to the exclusion. Therefore each such e has an actual factor whose depth it does not divide, and gcd(p in T_j,h_p)=1. A singleton support has depth one, so the block itself is prime.")),
                    Paragraph(Text("Every actual factor is split and has exact Fibonacci rank 2r_j, hence 2r_j divides p-1. For every real X, choose j large enough that 2r_j+1>X. All factors of this block then exceed X, and the preceding exponent witness lies in that same block. For each fixed e>=2 these witnesses are infinite, since a finite set of natural primes would be bounded. A common natural divisor of the original depths over the entire tail p>X divides the gcd of this finite block and must be one. The tail statement allows depth one and higher depths not divisible by e; it does not select either case.")),
                    Paragraph(Text("Let all actual depths be at least H>=2. There must be at least two factors. Three or more contribute at least 3H>2H+1. Two factors contribute at least 2H, and equality 2H would make both depths H, contrary to gcd one. Thus their total multiplicity is at least 2H+1; equality forces exactly two depths H,H+1. The rank divisibility and the split residues p=1 or 4 modulo five give the lower bound b(r)=8r+1,4r+1,6r+1,2r+1 for r=1,2,3,4 modulo five respectively. Multiplying the prime powers yields B_j>=b(r_j)^(2H+1), so a strict reverse inequality forces an actual depth below H. At j=4, r_j=243 and b(r_j)=1459, and the exact comparisons are 1459^10 < B_4 = 7177905237579946589743592924684179 < 1459^11. Taking H=5 gives a factor of original depth at most four. The abstract depth vector (2,3) still has gcd one with both entries at least two. These deductions neither construct nor exclude an all-WSS block with heterogeneous depths. The multiplicity-five residue specialization is explained in the existing QuadraticPrimeRadicalKernel narrative."))),
                DescribeRole.Theorem))));
}
