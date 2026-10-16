using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.EulerGerm;

internal sealed class GoldenCandidateOrbitDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Analytic/EulerGerm/GoldenCandidateOrbit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "GoldenCandidateOrbit", H("Prime channels of the scaled golden candidate"), Blocks(
            Describe.Lean(
                DescribeId.Create("gc-orbit-two-prime-straddle"),
                DeclarationHandle.Create(Module + "gc_orbit_two_prime_straddle"),
                H("The prime-three candidate lies inside the golden window"),
                StatementSource.FromAuthor(Disp(And(
                    Less(Lower(), Orbit(D(3))),
                    Less(Orbit(D(3)), Upper()),
                    Less(Orbit(D(5)), Lower())))), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The supplier c is the fixed complex candidate of GermZeroCertificateReduction, whose real part lies in the certified prime-two golden window. Define goldenCandidateOrbitScale(p) = log(2)/log(p) and goldenCandidateOrbit(p) = goldenCandidateOrbitScale(p) * c.re for a prime p. The theorem places the prime-three value strictly between 1/(2*phi^3) and 1/phi^2, and the prime-five value strictly below the lower boundary.")),
                    Paragraph(Text("This is an exact arithmetic location result for this fixed candidate. The independent universal local-factor scaling theorem is available in "), Ref("D5/S3/Analytic/EulerGerm/LocalFactorUniversalScaling"), Text(". A location statement for c does not assert that c or any transported candidate is a local-factor zero, and it gives no RH conclusion."))
                ), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("scaled-gc-orbit-window-iff"),
                DeclarationHandle.Create(Module + "scaled_gc_orbit_window_iff"),
                H("Exactly primes two and three lie inside the window"),
                StatementSource.FromAuthor(Disp(new Formula.BindMany(
                    FormulaQuantifier.ForAll,
                    [new(FormulaIdentifier.Create("p"), Call("Primes", Seq(Mathbb, Grp(F.Id("N")))))],
                    new Formula.Logic(And(Less(Lower(), Orbit(F.Id("p"))),
                        Less(Orbit(F.Id("p")), Upper())), FormulaLogicOperator.Iff,
                        new Formula.Logic(Equal(Call("val", F.Id("p")), D(2)),
                            FormulaLogicOperator.Or, Equal(Call("val", F.Id("p")), D(3))))))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every p : Nat.Primes, the logarithmically scaled real part lies in the open golden window if and only if p.val = 2 or p.val = 3. There is no bound on p and no additional numerical premise. Primality excludes four; logarithm monotonicity and 2^9 < 5^4 exclude every prime at least five. The prime-three part uses the preceding straddle theorem, and the prime-two part uses the existing c_in_golden_window supplier.")),
                    Paragraph(Text("The estimates compare logarithms of positive real numbers. The inequalities log(3) < 2*log(2), (9/4)*log(2) < log(5), and 2 < 2*phi^3*c.re < 9/4 locate the prime-three and prime-five values. Logarithm monotonicity then excludes every prime at least five."))
                ), DescribeRole.Theorem)
        )));

    private static Formula Orbit(Formula prime) => Call("goldenCandidateOrbit", prime);
    private static Formula Lower() => new Formula.Fraction(D(1),
        Seq(D(2), Sp, Times, Sp, Varphi, Caret, Grp(D(3))));
    private static Formula Upper() => new Formula.Fraction(D(1),
        Seq(Varphi, Caret, Grp(D(2))));
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(params Formula[] values) =>
        values.Aggregate((left, right) => new Formula.Logic(left, FormulaLogicOperator.And, right));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
