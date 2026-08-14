using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit.Displacement;

internal sealed class GoldenSubstitutionOrbitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden substitution preserves prime support and admits uniform orbitwise error bounds.",
        H("Golden Substitution Orbit"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-substitution-hidden-product-nonzero"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Displacement/GoldenSubstitutionOrbit.nS_ne_zero"),
                H("The hidden product is always nonzero"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("nS"), Open, F.Id("n"), Close, Neq, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The hidden product is a finite product of powers of primes in the original "
                        + "factorization support. Every such prime is positive, so every factor is "
                        + "positive and the whole product is positive. The empty product cases, including "
                        + "the input zero, are therefore covered without a separate hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-substitution-prime-radical-invariance"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Displacement/GoldenSubstitutionOrbit.primeRadical_nS"),
                H("One substitution preserves the prime radical"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Operatorname, Grp(F.Id("rad")), Open,
                    F.Id("nS"), Open, F.Id("n"), Close, Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("rad")), Open, F.Id("n"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The factorization of nS maps goldenSubstStart across the original exponents. "
                        + "That map fixes zero and is injective because substitution starts are strictly "
                        + "increasing, so mapping the exponent range leaves the finite support unchanged. "
                        + "The products of the distinct supported primes, hence the radicals, are equal. "
                        + "This support argument also covers zero unconditionally."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-substitution-prime-radical-orbit-invariance"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Displacement/GoldenSubstitutionOrbit.primeRadical_nS_iterate"),
                H("Every orbit iterate preserves the prime radical"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("k"), Comma, Sp, F.Id("n"), InMacro,
                    Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Operatorname, Grp(F.Id("rad")), Open,
                    F.Id("nS"), Caret, Grp(F.Id("k")), Open, F.Id("n"), Close, Close,
                    Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("rad")), Open, F.Id("n"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Induction on the iterate count repeatedly applies the one-step radical invariance. "
                        + "The zeroth iterate is the identity, and composing one more nS leaves the radical "
                        + "fixed again. Thus the entire orbit remains on the same set of prime divisors."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-substitution-uniform-contraction-orbit-bound"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Displacement/GoldenSubstitutionOrbit.abs_lambdaMinus_nS_iterate_le"),
                H("The frozen contraction bound is uniform along the orbit"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("k"), Comma, Sp, F.Id("n"), InMacro,
                    Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("n"), Neq, D(0), Sp, Implies, Sp,
                    Lvert, LambdaLower, Underscore, Grp(Minus), Open,
                    F.Id("nS"), Caret, Grp(F.Id("k")), Open, F.Id("n"), Close, Close,
                    Rvert, Sp, Leq, Sp,
                    Varphi, Caret, Grp(Minus, D(1)), Sp, Cdot, Sp,
                    Log, Grp(Operatorname, Grp(F.Id("rad")), Open, F.Id("n"), Close)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every orbit point is nonzero when the starting value is nonzero: the zeroth point is "
                        + "the start, while every later point is an nS value and is always nonzero. The "
                        + "existing single-number contraction theorem applies at each point. Orbitwise "
                        + "radical invariance then replaces its radical by the one fixed at the start."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-substitution-accumulated-logarithmic-orbit-bound"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Displacement/GoldenSubstitutionOrbit.abs_log_nS_iterate_sub_goldenRatio_pow_mul_log_le"),
                H("Accumulated logarithmic displacement has a geometric bound"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("k"), Comma, Sp, F.Id("n"), InMacro,
                    Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("n"), Neq, D(0), Sp, Implies, Sp,
                    Lvert, Log, Grp(
                        F.Id("nS"), Caret, Grp(F.Id("k")), Open, F.Id("n"), Close),
                    Sp, Minus, Sp,
                    Varphi, Caret, Grp(F.Id("k")), Sp, Cdot, Sp,
                    Log, Grp(F.Id("n")), Rvert, Sp, Leq, Sp,
                    Left, Open, Varphi, Caret, Grp(F.Id("k")), Sp, Minus, Sp, D(1),
                    Right, Close, Sp, Cdot, Sp,
                    Log, Grp(Operatorname, Grp(F.Id("rad")), Open, F.Id("n"), Close)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At the next orbit point, the logarithmic displacement splits into the current "
                        + "contraction error plus phi times the displacement already accumulated. The "
                        + "triangle inequality, the uniform contraction bound, and the induction hypothesis "
                        + "therefore give a recurrence with one phi-inverse radical term per step. The "
                        + "identity phi minus phi inverse equals one converts that recurrence exactly into "
                        + "the coefficient phi to the kth power minus one."))),
                DescribeRole.Theorem))));
}
