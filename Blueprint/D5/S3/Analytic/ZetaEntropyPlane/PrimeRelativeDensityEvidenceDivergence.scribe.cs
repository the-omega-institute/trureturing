using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaEntropyPlane;

internal sealed class PrimeRelativeDensityEvidenceDivergenceDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Analytic/ZetaEntropyPlane/PrimeRelativeDensityEvidenceDivergence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Relative prime density zero does not force evidence summability.",
        H("Relative Prime Density and Evidence Divergence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-index-equivalence"),
                DeclarationHandle.Create(DeclarationPrefix + "primeIndexEquiv"),
                H("Natural numbers enumerate the primes"),
                StatementSource.FromAuthor(PrimeIndexEquivFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The increasing prime enumeration is packaged with its inverse prime "
                        + "index, so prime-relative counting can be expressed on natural "
                        + "indices."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("relative-prime-counting-ratio"),
                DeclarationHandle.Create(DeclarationPrefix + "relativePrimeCountingRatio"),
                H("Relative prime counting ratio"),
                StatementSource.FromAuthor(RelativeRatioFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The ratio counts selected prime indices in the first n entries of the "
                        + "prime enumeration and divides by n."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("square-indexed-prime-support"),
                DeclarationHandle.Create(DeclarationPrefix + "squareIndexedPrimeSupport"),
                H("Square-indexed prime support"),
                StatementSource.FromAuthor(SquareSupportFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The selected support consists of primes at square natural indices. Its "
                        + "first n members are bounded by the square-root scale."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("square-indexed-prime-evidence"),
                DeclarationHandle.Create(DeclarationPrefix + "squareIndexedPrimeEvidence"),
                H("Harmonic evidence on square-indexed primes"),
                StatementSource.FromAuthor(SquareEvidenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A square-indexed prime receives the reciprocal of its square-root index "
                        + "plus one; every other prime receives zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zero-cutoff-relative-ratio"),
                DeclarationHandle.Create(DeclarationPrefix + "relativePrimeCountingRatio_zero"),
                H("Every relative ratio is zero at the zero cutoff"),
                StatementSource.FromAuthor(ZeroCutoffFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At n equal to zero the counted range is empty and the totalized ratio is "
                        + "exactly zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("empty-relative-density-zero"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "empty_relative_prime_density_zero"),
                H("Empty support has relative density zero"),
                StatementSource.FromAuthor(EmptyDensityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The empty support gives the constant zero ratio. This is the explicit "
                        + "zero-density boundary witness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("full-relative-density-one"),
                DeclarationHandle.Create(DeclarationPrefix + "full_relative_prime_density_one"),
                H("Full support has relative density one"),
                StatementSource.FromAuthor(FullDensityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The universal support contains every enumerated prime, so its ratio is "
                        + "one away from the totalized zero cutoff."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("singleton-relative-density-and-summability"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "singleton_relative_prime_density_zero_and_summable"),
                H("Singleton support is density zero and summable"),
                StatementSource.FromAuthor(SingletonFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A singleton prime support has zero relative density and only one possible "
                        + "nonzero evidence term, for every real exponent."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("square-support-relative-density-zero"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "square_indexed_prime_support_relative_density_zero"),
                H("Square-indexed support has relative density zero"),
                StatementSource.FromAuthor(SquareDensityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The square support has at most square-root many hits among the first n "
                        + "prime indices, so its relative prime density tends to zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("square-evidence-not-summable"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "square_indexed_prime_evidence_not_summable"),
                H("Square-indexed harmonic evidence is divergent"),
                StatementSource.FromAuthor(SquareEvidenceDivergesFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Restricting the evidence to square indices exposes the harmonic series "
                        + "along an injective prime subsequence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-density-divergent-evidence"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "zero_relative_prime_density_with_divergent_evidence"),
                H("Zero relative density can carry divergent evidence"),
                StatementSource.FromAuthor(ZeroDensityDivergenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The square-indexed support simultaneously witnesses zero relative prime "
                        + "density and nonsummable cumulative evidence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-density-evidence-independence"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "prime_relative_density_does_not_determine_evidence_summability"),
                H("Relative prime density does not determine summability"),
                StatementSource.FromAuthor(IndependenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The theorem combines the earlier natural-density contrast with the new "
                        + "zero-relative-density divergent example and the full-density "
                        + "convergent witness."))),
                DescribeRole.Theorem))));

    private static Formula PrimeIndexEquivFormula() => Disp(Seq(
        F.Id("N"), Sp, Equiv, Sp, F.Id("NatPrimes")));

    private static Formula RelativeRatioFormula() => Disp(Equal(
        Call("r", F.Id("S"), F.Id("n")),
        new Formula.Fraction(
            Seq(
                Lvert, Sp, F.Id("k"), Sp, Lt, Sp, F.Id("n"), Sp, Mid, Sp,
                Call("primeIndexEquiv", F.Id("k")), Sp, InMacro, Sp, F.Id("S"), Sp, Rvert),
            F.Id("n"))));

    private static Formula SquareSupportFormula() => Disp(Equal(
        F.Id("Ssq"),
        Seq(OpenBrace, Call("primeIndexEquiv", Call("square", F.Id("k"))),
            Sp, Mid, Sp, F.Id("k"), Sp, InMacro, Sp, F.Id("N"), CloseBrace)));

    private static Formula SquareEvidenceFormula()
    {
        Formula prime = F.Id("p");
        Formula denominator = Seq(
            Open, Call("sqrt", Call("index", prime)), Sp, Plus, Sp, D(1), Close);
        Formula value = new Formula.Fraction(D(1), denominator);
        Formula condition = new Formula.Relation(
            prime, FormulaRelationOperator.MemberOf, F.Id("Ssq"));
        return Disp(Equal(
            Call("esq", prime), Call("piecewise", condition, value, D(0))));
    }

    private static Formula ZeroCutoffFormula() => Disp(Seq(
        Forall, Sp, F.Id("S"), Comma, Sp,
        Equal(Call("r", F.Id("S"), D(0)), D(0))));

    private static Formula EmptyDensityFormula() => Disp(DensityLimit(Emptyset, D(0)));

    private static Formula FullDensityFormula() => Disp(DensityLimit(F.Id("univ"), D(1)));

    private static Formula SingletonFormula() => Disp(Seq(
        Forall, Sp, F.Id("q"), Comma, Sp, F.Id("s"), Comma, Sp,
        And(
            DensityLimit(SingletonSet(F.Id("q")), D(0)),
            IsSummable(Call("e", SingletonSet(F.Id("q")), F.Id("s"))))));

    private static Formula SquareDensityFormula() => Disp(
        DensityLimit(F.Id("Ssq"), D(0)));

    private static Formula SquareEvidenceDivergesFormula() => Disp(
        Not(IsSummable(F.Id("esq"))));

    private static Formula ZeroDensityDivergenceFormula() => Disp(And(
        DensityLimit(F.Id("Ssq"), D(0)),
        Not(IsSummable(F.Id("esq")))));

    private static Formula IndependenceFormula() => Disp(And(
        F.Id("countingDensityContrast"),
        And(
            ZeroDensityDivergenceFormula(),
            And(
                DensityLimit(F.Id("univ"), D(1)),
                IsSummable(F.Id("primeEvidence2"))))));

    private static Formula DensityLimit(Formula support, Formula value) => Seq(
        Lim, Underscore, Grp(F.Id("n"), To, Infty), Sp,
        Call("r", support, F.Id("n")), Sp, Eq, Sp, value);

    private static Formula IsSummable(Formula family) => new Formula.Apply(
        F.Id("Summable"), [family]);

    private static Formula SingletonSet(Formula value) => Seq(
        OpenBrace, value, CloseBrace);

    private static Formula And(Formula left, Formula right) => new Formula.Logic(
        left, FormulaLogicOperator.And, right);

    private static Formula Not(Formula value) => Seq(Neg, Sp, value);
}
