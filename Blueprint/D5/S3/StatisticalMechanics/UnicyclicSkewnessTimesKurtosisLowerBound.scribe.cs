using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class UnicyclicSkewnessTimesKurtosisLowerBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/UnicyclicSkewnessTimesKurtosisLowerBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/ptaszynski2022skewness");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The product of skewness and kurtosis of every finite positive unidirectional cycle strictly exceeds its greatest lower bound over all cycle sizes.",
        H("The sharp lower bound on unicyclic skewness times kurtosis"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("lower-bound"), DeclarationHandle.Create(Prefix + "lowerBound"),
                H("The exact asymptotic lower endpoint"),
                StatementSource.FromAuthor(Disp(LowerBoundFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The real constant lowerBound is the infimum, over positive real A, of "
                    + "(1 − 10A + 22A² − 12A³)/(1 + A)⁸. Ptaszyński's arXiv v4 main.tex "
                    + "line 445 gives this expression for the product endpoint. Lines 438-440 "
                    + "give its approximate value −0.054, and line 424 specifies the asymptotic "
                    + "family with one relative rate a = A/N as N tends to infinity. "
                    + "The infimum specifies the exact constant without rounding."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("Strict finite-cycle inequality and greatest lower bound"),
                StatementSource.FromAuthor(Disp(Equivalence(Typed(Local("claim"), Qualified("Prop")), ClaimBody()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural n ≥ 2 and every strictly positive real k : Fin n → ℝ, "
                    + "the product skewness k times kurtosis k strictly exceeds lowerBound. "
                    + "This same constant is the greatest lower bound of all these products, "
                    + "with n unbounded and both factors evaluated on the same rate vector. "
                    + "Repeated rates are allowed. The source gives the rounded product interval "
                    + "in main.tex lines 129-137 and the exact endpoint in lines 443-446; "
                    + "line 792 calls the universal extremal-topology assertion a numerical conjecture. "
                    + "Here its lower endpoint is read as an infimum for unidirectional cycles, "
                    + "with strictness at every finite size. The assertion concerns the inverse-rate "
                    + "expressions for skewness and kurtosis; it does not construct a stochastic "
                    + "process or prove its renewal asymptotics. The upper endpoint, bidirectional "
                    + "cycles and a finite-size optimizing topology are outside this statement."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The universal strict bound and sharpness"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Put E(A) = (1 − 10A + 22A² − 12A³)/(1 + A)⁸ and "
                        + "F(u) = u⁵(3u − 2)(15u² − 20u + 6). "
                        + "For A > 0 the denominator of E(A) is positive, and expanding "
                        + "100(1 + A)⁸ + 1 − 10A + 22A² − 12A³ gives a polynomial with "
                        + "nonnegative coefficients. Hence E(A) ≥ −100, so its values are "
                        + "bounded below and lowerBound ≤ E(A). For 0 < u < 1, substitution "
                        + "A = (1 − u)/u gives E(A) = F(u), whence lowerBound ≤ F(u). "
                        + "Taking A = 1/4 gives lowerBound ≤ −4096/78125 < −3/80 < 0. "
                        + "Also, if 0 < t < z and H(z) = z(3z − 2)(15z² − 20z + 6) < 0, "
                        + "then t⁴ < z⁴ reverses direction on multiplication by H(z), giving "
                        + "t⁴H(z) > z⁴H(z) = F(z).")),
                    Paragraph(Text(
                        "For a rate vector k, write Rⱼ = ∑ᵢ(kᵢ)⁻ʲ, "
                        + "xᵢ = (kᵢ)⁻¹/R₁, p = ∑ᵢxᵢ², q = ∑ᵢxᵢ³ and r = ∑ᵢxᵢ⁴. "
                        + "The skewness and kurtosis normalization identities give "
                        + "S = 3p² − 2q and K = 15p² − 20q + 6r/p, so their product "
                        + "is the product of these two expressions. If SK ≥ 0, the negativity "
                        + "of lowerBound already gives SK > lowerBound.")),
                    Paragraph(Text(
                        "Suppose p > 0, r < p² and −1/16 ≤ S < 0 < K. "
                        + "Then r/p < p and 3p² < 2q, so "
                        + "K < 6p − 15p² ≤ 3/5. The last inequality follows from "
                        + "3/5 − (6p − 15p²) = (3/5)(5p − 1)². "
                        + "Multiplying S ≥ −1/16 by K > 0 gives SK ≥ −K/16 > −3/80. "
                        + "Since lowerBound < −3/80, this case also gives the strict bound.")),
                    Paragraph(Text(
                        "For the remaining negative-product case assume S > 0 > K, "
                        + "p > 0, q² ≤ pr, r < p² and p² ≤ q. Set t = q/p and z = p²/q. "
                        + "Then q > 0, t > 0, z > 0 and q² ≤ pr < p³ gives t < z; "
                        + "p² ≤ q gives z ≤ 1. Moreover p = tz, q = t²z and t² ≤ r/p. "
                        + "Thus K₀ = 15p² − 20q + 6t² ≤ K < 0. "
                        + "The identities S = t²z(3z − 2) and "
                        + "K₀ = t²(15z² − 20z + 6) show H(z) < 0. "
                        + "In particular z ≠ 1, since H(1) = 1, so 0 < z < 1. "
                        + "Multiplication of K₀ ≤ K by S > 0 yields "
                        + "SK ≥ SK₀ = t⁴H(z) > F(z) ≥ lowerBound. "
                        + "The strict comparison uses t < z and the negative sign of H(z).")),
                    Paragraph(Text(
                        "To supply these moment hypotheses for every n ≥ 2 and positive k, "
                        + "the joint normalized-moment inequalities give p > 0, q² ≤ pr and r < p². "
                        + "The normalized inverse rates are nonnegative and sum to one. "
                        + "Cauchy-Schwarz applied to xᵢ², xᵢ and xᵢ³, using "
                        + "(xᵢ²)² = xᵢxᵢ³ and ∑ᵢxᵢ = 1, gives p² ≤ q. "
                        + "The finite-size skewness minimum is "
                        + "−(8 − 8(n : ℝ) + (n : ℝ)²)/(16((n : ℝ) − 1)²). "
                        + "Its difference from −1/16 is "
                        + "(6(n : ℝ) − 7)/(16((n : ℝ) − 1)²) ≥ 0, since n ≥ 2; "
                        + "the skewness minimum theorem "
                        + "therefore supplies S ≥ −1/16. Now split first on SK ≥ 0. "
                        + "If SK < 0, either S < 0 < K or S > 0 > K. "
                        + "The preceding arguments prove SK > lowerBound in every case.")),
                    Paragraph(Text(
                        "For sharpness, fix 0 < u < 1 and a natural m ≥ 1. "
                        + "Take m + 1 rates, with k₀ = (1 − u)/((m : ℝ)u) "
                        + "and kᵢ = 1 for i ≠ 0. All rates are positive, and "
                        + "Rⱼ = ((m : ℝ)u/(1 − u))ʲ + (m : ℝ) for every natural j. "
                        + "Substitution in the two inverse-rate expressions gives "
                        + "SK = (3Pᵤ(v)² − 2Qᵤ(v))(15Pᵤ(v)² − 20Qᵤ(v) + 6Tᵤ(v)/Pᵤ(v)) "
                        + "at v = 1/(m : ℝ), where "
                        + "Pᵤ(v) = u² + (1 − u)²v, Qᵤ(v) = u³ + (1 − u)³v² "
                        + "and Tᵤ(v) = u⁴ + (1 − u)⁴v³. "
                        + "This expression is continuous at v = 0, since Pᵤ(0) = u² > 0, "
                        + "and its value there is F(u). Replacing m by m + 1 makes "
                        + "v = 1/((m + 1 : ℕ) : ℝ) tend to zero. Thus the products "
                        + "for these positive cycles of size m + 2 tend to F(u).")),
                    Paragraph(Text(
                        "It remains to choose u with F(u) = lowerBound. The polynomial F "
                        + "is continuous, so it attains a minimum on the nonempty compact interval [0,1]. "
                        + "Since F(4/5) = −4096/78125 < 0, a minimizer u has F(u) < 0. "
                        + "The endpoint values F(0) = 0 and F(1) = 1 force 0 < u < 1. "
                        + "The substitution already gives lowerBound ≤ F(u). Conversely, for "
                        + "each A > 0 take v = 1/(1 + A). Then 0 < v < 1, "
                        + "(1 − v)/v = A and E(A) = F(v) ≥ F(u) by minimality. "
                        + "Thus F(u) is a lower bound for the nonempty set of E(A), A > 0, "
                        + "and F(u) ≤ its infimum lowerBound. Consequently F(u) = lowerBound.")),
                    Paragraph(Text(
                        "Finally the strict inequality makes lowerBound a lower bound of "
                        + "the set in the statement. Any other lower bound b is no greater "
                        + "than every product in the positive family of cycles of size m + 2 "
                        + "at the minimizing u. Passing to its limit F(u) = lowerBound gives "
                        + "b ≤ lowerBound. This proves the greatest-lower-bound assertion "
                        + "together with the strict finite-cycle inequality."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ptaszynski-2022-unidirectional-skewness-times-kurtosis-lower-bound"),
                    ResolutionKind.Proved)))));

    private static Formula LowerBoundFormula() => Equal(Typed(Local("lowerBound"), Reals()),
        At(Qualified("InfSet", "sInf"), At(Qualified("Set", "image"),
            LambdaOf("A", Reals(), Divide(
                Subtract(Add(Subtract(Real(1), Multiply(Real(1, 0), X("A"))),
                    Multiply(Real(2, 2), Power(X("A"), Natural(2)))),
                    Multiply(Real(1, 2), Power(X("A"), Natural(3)))),
                Power(Add(Real(1), X("A")), Natural(8)))),
            At(Qualified("Set", "Ioi"), Real(0)))));

    private static Formula ClaimBody()
    {
        Formula strict = All("n", Naturals(), Implication(LessEqual(Natural(2), X("n")),
            All("k", RateType(), Implication(PositiveRates(),
                Less(Local("lowerBound"), ProductValue())))));
        Formula values = Seq(OpenBrace, Typed(X("s"), Reals()), Sp, Mid, Sp,
            Some("n", Naturals(), Conjunction(LessEqual(Natural(2), X("n")),
                Some("k", RateType(), Conjunction(PositiveRates(), Equal(X("s"), ProductValue()))))),
            CloseBrace);
        return Conjunction(strict, At(Qualified("IsGLB"), values, Local("lowerBound")));
    }

    private static Formula ProductValue() => Multiply(
        At(Qualified("D5", "S3", "StatisticalMechanics", "UnicyclicSkewnessMinimum", "skewness"), X("k")),
        At(Qualified("D5", "S3", "StatisticalMechanics", "UnicyclicKurtosisLowerBound", "kurtosis"), X("k")));
    private static Formula PositiveRates() =>
        All("i", FinOf(X("n")), Less(Real(0), At(X("k"), X("i"))));
    private static Formula Local(string name) =>
        Qualified("D5", "S3", "StatisticalMechanics", "UnicyclicSkewnessTimesKurtosisLowerBound", name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula X(string name) => F.Id(name);
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Natural(params byte[] digits) => Typed(D(digits), Naturals());
    private static Formula Real(params byte[] digits) => Typed(D(digits), Reals());
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);
    private static Formula RateType() => new Formula.TypeArrow(FinOf(X("n")), Reals());
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(Qualified("fun"), Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LessEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implication(Formula left, Formula right) =>
        new Formula.TypeArrow(Parenthesized(left), Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula Divide(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
}
