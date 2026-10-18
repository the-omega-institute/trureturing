using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class LatticeWalkCrossIntegralRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Dynamics/LatticeWalkCrossIntegralRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/dhamapurkar2023latticemixing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Early coherent amplitudes contradict the uniform lattice-walk cross-integral estimate.",
        H("The lattice-walk cross-integral estimate fails"), Blocks(
            Paragraph(Text(
                "All finite indices are natural numbers, i is the imaginary unit, and log is the "
                    + "natural logarithm. Integrals use Lebesgue measure on the real time axis, "
                    + "and the norm of a complex number is its modulus. In the exponentials, "
                    + "the indices are embedded in the real or complex numbers before subtraction, "
                    + "so j − k is the signed difference.")),
            Node("walkTerm", "The oscillatory term of the cycle walk", WalkTermFormula(),
                "For every natural n, integer displacement l and real time t, walkTerm(n,l,t) "
                    + "is the complex double sum in Eq. (B8). It omits the diagonal j = k and "
                    + "the antidiagonal j + k = n. The last exponential equals w raised to "
                    + "l(j − k), where w = exp(2πi/n), so l is the displacement q − p. "
                    + "When n = 0 both index ranges are empty and the sum is zero."),
            Node("claim", "The proposed uniform cross-integral bound", ClaimFormula(),
                "Equation (15), the two-dimensional estimate used after Conjecture 1, asserts "
                    + "this bound for every pair of odd, coprime natural orders n₁ > n₂, every "
                    + "pair of natural displacements l₁ < n₁ and l₂ < n₂, and every real T ≥ 0. "
                    + "The two factors are evaluated at the same time t. The right side is "
                    + "32n₁(n₂ log n₂)² + 32n₂(n₁ log n₁)² and is independent of T."),
            Describe.Lean(
                DescribeId.Create("lattice-walk-cross-integral-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A counterexample at unit time"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Named("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take n₂ = 10¹⁰ + 1, n₁ = 10¹⁰ + 3, l₁ = l₂ = 1 and T = 1. "
                            + "The two orders are odd and coprime: any common divisor divides "
                            + "their difference 2, and an odd number has no even divisor. "
                            + "Both displacements lie in the required ranges.")),
                    Paragraph(Text(
                        "For an odd natural n ≥ 3 and real t, write "
                            + "A_n(t) = Σ_{0≤j<n} exp(i(t/2)cos(2πj/n)) exp(2πij/n). "
                            + "The cosine difference identity expands |A_n(t)|² into the full "
                            + "double sum. Its diagonal contributes n. Its antidiagonal, "
                            + "disjoint from the diagonal for odd n, contributes −1 by the sum "
                            + "of the nontrivial powers of exp(4πi/n). Consequently "
                            + "walkTerm(n,1,t) = |A_n(t)|² − (n − 1), a real number.")),
                    Paragraph(Text(
                        "For every natural n ≥ 3, pairing j with n − j cancels the "
                            + "sine-cosine cross terms in the imaginary part of A_n(t). "
                            + "The identity Σ_{0≤j<n} cos²(2πj/n) = n/2 and the inequality "
                            + "u sin u ≥ u²/2 for |u| ≤ 1/2 give Im A_n(t) ≥ nt/8 "
                            + "for 0 < t ≤ 1. Hence |A_n(t)|² ≥ n²/256 on [1/2,1]. "
                            + "The triangle inequality also gives 0 ≤ |A_n(t)|² ≤ n² "
                            + "for every real t.")),
                    Paragraph(Text(
                        "For odd n₁,n₂ ≥ 3, expand the product using these two real "
                            + "identities. Bound each subtracted squared modulus by nᵢ² and "
                            + "discard the nonnegative constant (n₁ − 1)(n₂ − 1). "
                            + "The product of the squared moduli is nonnegative on [0,1] "
                            + "and at least n₁²n₂²/65536 on [1/2,1]. Thus its real integral "
                            + "satisfies ∫₀¹ walkTerm(n₁,1,t)walkTerm(n₂,1,t) dt "
                            + "≥ n₁²n₂²/131072 − (n₁ − 1)n₂² − (n₂ − 1)n₁².")),
                    Paragraph(Text(
                        "At the stated orders, 0 ≤ log n₂ ≤ log n₁ ≤ 34 log 2 < 24, "
                            + "since n₁ < 2³⁴. The proposed upper bound is therefore at most "
                            + "32·24²(n₁n₂² + n₂n₁²), which is strictly smaller than the "
                            + "integral lower bound above. The norm of the integral is at "
                            + "least its real value, contradicting Eq. (15)."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("dhamapurkar-deng-2023-lattice-walk-cross-integral-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("lattice-walk-cross-integral-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Named(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula NumberSet(string letter) => Seq(Mathbb, Grp(F.Id(letter)));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LT(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Square(Formula value) => new Formula.Power(Parenthesized(value), D(2));
    private static Formula SumOver(Formula index, Formula body) =>
        Seq(new Formula.Subscript(Sum, index), Sp, Parenthesized(body));
    private static Formula Range(Formula index, Formula n) =>
        Seq(Typed(index, NumberSet("N")), Comma, Sp, LE(D(0), index), Comma, Sp, LT(index, n));
    private static Formula IntervalIntegral(Formula upper, Formula variable, Formula body) =>
        Seq(new Formula.Subscript(Int, D(0)), Caret, Grp(upper), Sp,
            Parenthesized(body), Sp, F.Id("d"), variable);

    private static Formula WalkTermFormula()
    {
        Formula n = F.Id("n"), l = F.Id("l"), t = F.Id("t");
        Formula j = F.Id("j"), k = F.Id("k");
        Formula sineSum = At(Sin, new Formula.Fraction(Multiply(Pi, Parenthesized(Add(j, k))), n));
        Formula sineDifference = At(Sin,
            new Formula.Fraction(Multiply(Pi, Parenthesized(Subtract(j, k))), n));
        Formula oscillation = new Formula.Negate(Parenthesized(
            Multiply(Multiply(Multiply(F.Id("i"), t), sineSum), sineDifference)));
        Formula displacement = new Formula.Fraction(
            Multiply(Multiply(Multiply(Multiply(D(2), Pi), F.Id("i")), l),
                Parenthesized(Subtract(j, k))), n);
        Formula indices = Seq(Range(k, n), Comma, Sp,
            And(NotEqual(j, k), NotEqual(Add(j, k), n)));
        Formula sum = SumOver(Range(j, n), SumOver(indices,
            Multiply(At(Exp, oscillation), At(Exp, displacement))));
        return All(n, NumberSet("N"), All(l, NumberSet("Z"), All(t, NumberSet("R"),
            Equal(Call("walkTerm", n, l, t), sum))));
    }

    private static Formula ClaimFormula()
    {
        Formula nOne = new Formula.Subscript(F.Id("n"), D(1));
        Formula nTwo = new Formula.Subscript(F.Id("n"), D(2));
        Formula lOne = new Formula.Subscript(F.Id("l"), D(1));
        Formula lTwo = new Formula.Subscript(F.Id("l"), D(2));
        Formula t = F.Id("t"), upper = F.Id("T");
        Formula integral = IntervalIntegral(upper, t,
            Multiply(Call("walkTerm", nOne, lOne, t), Call("walkTerm", nTwo, lTwo, t)));
        Formula bound = Add(
            Multiply(Multiply(D(3, 2), nOne), Square(Multiply(nTwo, At(Log, nTwo)))),
            Multiply(Multiply(D(3, 2), nTwo), Square(Multiply(nOne, At(Log, nOne)))));
        Formula estimate = All(upper, NumberSet("R"),
            Imp(LE(D(0), upper), LE(new Formula.Norm(integral), bound)));
        estimate = All(lOne, NumberSet("N"), All(lTwo, NumberSet("N"),
            Imp(LT(lOne, nOne), Imp(LT(lTwo, nTwo), estimate))));
        estimate = All(nOne, NumberSet("N"), All(nTwo, NumberSet("N"),
            Imp(Call("Odd", nOne), Imp(Call("Odd", nTwo),
            Imp(Equal(At(Gcd, nOne, nTwo), D(1)), Imp(LT(nTwo, nOne), estimate))))));
        return new Formula.Logic(Named("claim"), FormulaLogicOperator.Iff, Parenthesized(estimate));
    }
}
