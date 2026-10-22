using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZeroData;

internal sealed class ActualReciprocalSquareBoundsDocument : IScribeDocumentDefinition
{
    private static Formula Nat => Seq(Mathbb, Grp(FormulaDsl.Id("N")));
    private static Formula Real => Seq(Mathbb, Grp(FormulaDsl.Id("R")));
    private static Formula Complex => Seq(Mathbb, Grp(FormulaDsl.Id("C")));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);

    private static Formula Then(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Absolute(Formula value) => new Formula.Absolute(value);

    private static Formula SetOfNat(string variable, Formula predicate) =>
        Seq(Left, OpenBrace, DefinitionDsl.Id(variable), Colon, Nat, Sp, Mid, Sp, predicate, Right, CloseBrace);

    private static Formula CountBothFormula()
    {
        var t = DefinitionDsl.Id("T");
        var k = DefinitionDsl.Id("k");
        var ordinate = Absolute(Call("im", Call("actualZero", k)));
        var cutoff = SetOfNat("k", AtMost(ordinate, t));
        var left = Call("ncard", cutoff);
        var right = new Formula.Floor(Multiply(new Formula.Number(2), Power(t, new Formula.Number(2))));
        return All("T", Real, Then(AtMost(new Formula.Number(10), t), AtMost(left, right)));
    }

    private static Formula HeightFormula()
    {
        var rho = DefinitionDsl.Id("rho");
        return All("rho", Complex,
            Then(Call("IsNontrivialZero", rho),
                Less(new Formula.Number(10), Absolute(Call("im", rho)))));
    }

    public DocumentDefinition Create()
    {
        return DocumentDefinition.Create(ScribeNode.Create(
            "Actual multiplicity-exact zero mass and unconditional height-ten exclusion from the first xi resolvent at six.",
            H("Actual Zeta Mass and Height"),
            Blocks(
                Paragraph(Text(
                    "The exact source family is actualData = zetaZeroData, with " +
                    "the real kernel pairWeight rho = Re(1/(rho*(1-rho))), and " +
                    "firstLiMass = 2 + EulerGamma - 2*log(2*sqrt(pi)). " +
                    "The normalized reflection and resolvent-positive R(6) chain uses " +
                    "sixWeight, sixDefect, the digamma-at-3 and H512 reductions, " +
                    "log(pi) and log(2) bounds, the complete von Mangoldt prime-power series, " +
                    "and the tail integral 1/648. The complex HasSum at six is consumed by the " +
                    "real HasSum for sixWeight; the positive kernel estimate and the evaluated defect " +
                    "are then consumed by the height contradiction.")),
                Paragraph(Text(
                    "The natural-index enumeration is equivalent to the sigma family of Fin (actualData.multiplicity n) over " +
                    "the exhaustive actual family. ActualZeroOccurrence, its infinite instance, " +
                    "actualOccurrenceEquiv : N ≃ ActualZeroOccurrence, actualZero, the exact fiber " +
                    "identity and fiber cardinality give exact transports of the infinite mass and " +
                    "the finite inclusive cutoffs. The resulting family includes both imaginary signs and every positive " +
                    "analytic multiplicity. The reciprocal-square summability and strict total bound " +
                    "are transported through those fibers; actual_count_both applies them to the " +
                    "literal cutoff |Im(actualZero k)| ≤ T and gives ncard ≤ floor(2*T^2) for " +
                    "every T ≥ 10, without a filtered family or RH premise.")),
                Describe.Lean(
                    DescribeId.Create("actualreciprocalsquarebounds"),
                    DeclarationHandle.Create("D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.actual_count_both"),
                    H("Actual Inverse Square Mass and Literal Cutoffs"),
                    StatementSource.FromAuthor(Disp(CountBothFormula())),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The displayed telescope binds the real cutoff T and retains its hypothesis " +
                        "10 ≤ T. The set is exactly the natural-index set {k : N | |im(actualZero k)| ≤ T}; " +
                        "its cardinality is bounded by the natural floor of 2*T^2. The proof consumes " +
                        "actual_inverse_square_summable, actual_inverse_square_mass_lt_two, " +
                        "mem_actualNatCutoff, actual_cutoff_sum_transport, " +
                        "actual_cutoff_card_by_fiber, and actual_finite_count_shell. The finite " +
                        "cutoff remains inclusive, and the bound is a conclusion of the exact family, " +
                        "not an assumed mass or height certificate."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("actualheightgtten"),
                    DeclarationHandle.Create("D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.actual_height_gt_ten"),
                    H("First Resolvent at Six"),
                    StatementSource.FromAuthor(Disp(HeightFormula())),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The displayed telescope binds an arbitrary complex rho and assumes only the " +
                        "actual predicate IsNontrivialZero rho; its conclusion is exactly " +
                        "10 < |rho.im|. The proof first obtains the endpoint estimate S < 1/3 and " +
                        "the conjugate-pair bootstrap u > 5. The normalized resolvents at 1 and 6, " +
                        "the multiplicity-preserving reflection permutation, and the rational identity " +
                        "produce T6 = 165 * sum_n multiplicity(n) * sixWeight(zero n). The lower " +
                        "kernel is 9/(10*(u+1)*(u+31)); a zero with u ≤ 100 forces " +
                        "T6 ≥ 297/13231. Factorization at six gives " +
                        "T6 = 593/60 + 6*EulerGamma - 11*log(2) - 5*log(pi) + Q6; " +
                        "the H512 estimate, the one-term logarithm lower bound, all von Mangoldt " +
                        "prime powers, and the integrable tail 1/648 give " +
                        "T6 < 329/15000, a strict contradiction. Exhaustivity then transfers " +
                        "100 < (Im(zero n))^2 to the arbitrary rho. No height, mass, numerical, " +
                        "critical-line, or RH premise is introduced. " +
                        "These numerical reductions bound the same complete analytic quantities: " +
                        "firstLiMass_lt_one proves firstLiMass < 1, excluding real zeros and making " +
                        "conjugate indices distinct; firstLiMass_lt_third proves firstLiMass < 1/3 " +
                        "for the bootstrap u > 5. At the resolvent parameter 6, gamma_upper_r6 proves " +
                        "EulerGamma < 5787/10000, log_pi_lower_r6 proves 11447/10000 < log(pi), " +
                        "and Real.log_two_gt_d9 implies 6931/10000 < log(2). " +
                        "These upper, lower, and lower bounds have the directions required by " +
                        "the coefficients +6, -5, and -11. The gamma bound uses the exact harmonic " +
                        "sum H512 and log(512) = 9*log(2). The bound sixQ_upper proves Q6 < 7/500 " +
                        "for the actual Re(-zeta'(6)/zeta(6)), using its complete von Mangoldt " +
                        "series and every term with n >= 4 in the tail comparison. The bound " +
                        "sixDefect_upper combines these estimates to give T6 < 329/15000 for " +
                        "the same defect. The proof actual_ordinate_sq_gt_hundred consumes this " +
                        "bound with the low-zero lower bound, and actual_height_gt_ten transfers " +
                        "the contradiction to every actual nontrivial zero."))),
                    DescribeRole.Theorem),
                Paragraph(Text(
                    "For every m ≥ 1, the CompleteZeroFamily fields are supplied by the exact zero, strip, " +
                    "height, reciprocal-square summability, reciprocal-square mass < 2, finite " +
                    "count shell, and count bound above. For an actual rho, it sets " +
                    "gamma = |Im rho|, so actual_height_gt_ten supplies gamma > 10. " +
                    "The application of complete_low_h_weighted_mean_bound uses " +
                    "the scalar hypothesis m ≥ 1 and the bound " +
                    "m*(gamma+10)^2*(2400000*exp(-83*m) + 2400 + 384*exp(-28*m)). " +
                    "Here the inner h-domain is the full Icc 0 2 with weight 1+h, whose integral is 4; " +
                    "the Gaussian center is 16*m with variance denominator 4*m; the physical envelope " +
                    "has coefficient 3; and the shell estimate has core coefficient 20, " +
                    "giving 3*4*20 = 240 and the 2400000*exp(-83*m) term. The positive and negative " +
                    "extensions are 2400 and 384*exp(-28*m).")),
                Paragraph(Text(
                    "The proof uses endpoint " +
                    "normalization, strip and conjugation algebra, occurrence and fiber transports, " +
                    "finite cutoff membership, the real-part HasSum, kernel positivity, and the " +
                    "von Mangoldt tail comparison.")))));
    }
}

