using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.PrimeProducts;

internal sealed class ZetaPrimeObservationSynthesisDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/PrimeProducts/ZetaPrimeObservationSynthesis.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The zeta Gibbs law unifies exact prime spectra, information, and observation limits.",
        H("Zeta Prime-Observation Synthesis"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("countable-hellinger-affinity-definition"),
                DeclarationHandle.Create(Prefix + "countableHellingerAffinity"),
                H("Countable Hellinger affinity"),
                StatementSource.FromAuthor(AffinityDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The countable affinity is the sum of square roots of pointwise PMF "
                        + "mass products. It extends the repository's finite affinity formula "
                        + "to the natural-number carrier used by the zeta law."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-residual-law-definition"),
                DeclarationHandle.Create(Prefix + "primeResidualLaw"),
                H("Prime residual law at a precision threshold"),
                StatementSource.FromAuthor(ResidualLawFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Condition the geometric exponent channel on values at least k, then "
                        + "translate the observed tail back by k. The resulting PMF names the "
                        + "unresolved exponent law after k precision layers."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-residual-entropy-definition"),
                DeclarationHandle.Create(Prefix + "primeResidualEntropy"),
                H("Probability-weighted prime residual entropy"),
                StatementSource.FromAuthor(ResidualEntropyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Residual entropy is the tail probability multiplied by the Shannon "
                        + "entropy of the translated conditional residual law."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-diagonal-phase-blindness-definition"),
                DeclarationHandle.Create(Prefix + "PrimeDiagonalPhaseBlindness"),
                H("Prime-indexed diagonal observables are phase blind"),
                StatementSource.FromAuthor(PhaseBlindnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every prime-indexed family of diagonal qubit observables gives the same "
                        + "joint readout on the canonical distinct relative-phase pair."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-exponent-pmf-equals-thermal-pmf"),
                DeclarationHandle.Create(
                    Prefix + "primeExponentPMF_eq_singlePrimeThermalPMF"),
                H("Prime exponents have the single-mode thermal spectrum"),
                StatementSource.FromAuthor(ThermalBridgeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every prime and s greater than one, the geometric exponent PMF is "
                        + "exactly the named single-prime thermal PMF, pointwise at every "
                        + "occupation number."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zeta-hellinger-affinity-prime-product"),
                DeclarationHandle.Create(
                    Prefix + "countableHellingerAffinity_zeta_eq_tprod_prime"),
                H("Zeta Hellinger affinity factors over prime modes"),
                StatementSource.FromAuthor(HellingerProductFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For two normalizable zeta parameters, the global countable affinity is "
                        + "the convergent infinite product of the geometric prime-coordinate "
                        + "affinities. Euler-log summability licenses the product."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zeta-prime-observation-synthesis"),
                DeclarationHandle.Create(Prefix + "zeta_prime_observation_synthesis"),
                H("FPOD theorem 145.1 on the available carriers"),
                StatementSource.FromAuthor(SynthesisFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Above one, prime valuations separate positive integers and are "
                            + "independent geometric coordinates. Their product law has finite "
                            + "support almost surely and uniquely realizes the zeta masses.")),
                    Paragraph(Text(
                        "Shannon entropy, real-valued log evidence, and Hellinger affinity have "
                            + "exact prime decompositions. The Fisher component records the "
                            + "proved summable prime sensitivity family; no unproved global "
                            + "score-variance identity is asserted.")),
                    Paragraph(Text(
                        "Residual entropy contracts by p^(-s). The Fock clause is represented "
                            + "by independent prime modes with exact thermal PMF spectra and "
                            + "modal entropy additivity, not by an unavailable countable "
                            + "trace-class tensor-product operator.")),
                    Paragraph(Text(
                        "The complete valuation language identifies classical positive "
                            + "integers, while every prime-indexed diagonal qubit family is "
                            + "blind to the named relative-phase pair."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("one-lt-is-necessary"),
                DeclarationHandle.Create(Prefix + "one_lt_is_necessary"),
                H("The lower boundary is necessary"),
                StatementSource.FromAuthor(BoundaryCounterexampleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At the concrete critical parameter s = 1, no PMF on positive integers "
                        + "realizes the independent geometric prime-exponent law."))),
                DescribeRole.Theorem))));

    private static Formula AffinityDefinitionFormula()
    {
        Formula p = F.Id("P");
        Formula q = F.Id("Q");
        Formula n = F.Id("n");
        Formula summand = Seq(
            Sqrt, Grp(Call("pmfReal", p, n), Sp, Cdot, Sp,
                Call("pmfReal", q, n)));
        Formula sum = Seq(
            Sum, Underscore, Grp(n, Sp, InMacro, Sp, Naturals()), Sp, summand);
        return Disp(Equal(Affinity(p, q), sum));
    }

    private static Formula ThermalBridgeFormula()
    {
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula premise = Seq(
            D(1), Sp, Lt, Sp, s, Sp, Land, Sp,
            p, Sp, InMacro, Sp, Primes());
        Formula equality = Equal(
            Call("primeExponentPMF", s, p),
            Call("singlePrimeThermalPMF", p, s));
        return Disp(new Formula.Logic(
            premise, FormulaLogicOperator.Implies, equality));
    }

    private static Formula ResidualLawFormula()
    {
        Formula p = F.Id("p");
        Formula k = F.Id("k");
        Formula exponent = F.Id("E");
        Formula conditioned = Call("LawGiven",
            Seq(exponent, Sp, Minus, Sp, k),
            Seq(exponent, Sp, Geq, Sp, k));
        Formula residual = Seq(F.Id("R"), Underscore, Grp(p, Comma, Sp, k));
        return Disp(Equal(residual, conditioned));
    }

    private static Formula ResidualEntropyFormula()
    {
        Formula p = F.Id("p");
        Formula k = F.Id("k");
        Formula exponent = F.Id("E");
        Formula residual = Seq(F.Id("R"), Underscore, Grp(p, Comma, Sp, k));
        Formula left = Call("primeResidualEntropy", p, k);
        Formula right = Seq(
            Call("Pr", Seq(exponent, Sp, Geq, Sp, k)), Sp, Cdot, Sp,
            Call("H", residual));
        return Disp(Equal(left, right));
    }

    private static Formula PhaseBlindnessFormula()
    {
        Formula observable = F.Id("A");
        Formula p = F.Id("p");
        Formula plus = F.Id("rhoPlus");
        Formula minus = F.Id("rhoMinus");
        Formula diagonal = Seq(
            Forall, Sp, p, Comma, Sp,
            Call("IsDiag", Seq(observable, Open, p, Close)));
        Formula readoutEqual = Equal(
            Call("jointReadout", observable, plus),
            Call("jointReadout", observable, minus));
        Formula conclusion = And(
            new Formula.Relation(plus, FormulaRelationOperator.NotEqual, minus),
            readoutEqual);
        Formula quantified = Seq(
            Forall, Sp, observable, Comma, Sp,
            new Formula.Logic(diagonal, FormulaLogicOperator.Implies, conclusion));
        return Disp(quantified);
    }

    private static Formula HellingerProductFormula()
    {
        Formula s = F.Id("s");
        Formula t = F.Id("t");
        Formula p = F.Id("p");
        Formula premise = Seq(
            D(1), Sp, Lt, Sp, s, Sp, Land, Sp, D(1), Sp, Lt, Sp, t);
        Formula local = Affinity(
            Call("primeExponentPMF", s, p),
            Call("primeExponentPMF", t, p));
        Formula product = Seq(
            Prod, Underscore, Grp(p, Sp, InMacro, Sp, Primes()), Sp, local);
        Formula equality = Equal(
            Affinity(Call("zetaDist", s), Call("zetaDist", t)), product);
        return Disp(new Formula.Logic(
            premise, FormulaLogicOperator.Implies, equality));
    }

    private static Formula SynthesisFormula()
    {
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula k = F.Id("k");
        Formula information = And(
            Equal(Call("H", Call("zetaDist", s)),
                Call("tsumPrimeEntropy", s)),
            And(
                Equal(Call("KL", s, F.Id("t")),
                    Call("tsumPrimeKL", s, F.Id("t"))),
                And(Call("SummablePrimeFisherSensitivity", s),
                    Equal(Call("HellingerAffinity", s, F.Id("t")),
                        Call("tprodPrimeAffinity", s, F.Id("t"))))));
        Formula residual = Equal(
            Call("ResidualEntropy", p, Seq(k, Sp, Plus, Sp, D(1))),
            Seq(p, Caret, Grp(Minus, s), Sp, Cdot, Sp,
                Call("ResidualEntropy", p, k)));
        Formula conclusion = new Formula.Aligned([
            Call("Bijective", F.Id("primeExponentLanguageEquiv")),
            Call("IndependentPrimeExponents", Call("zetaDist", s)),
            Seq(Equal(Call("PrFiniteSupport", s), D(1))),
            Call("UniquePositiveIntegerLaw", Seq(F.Id("n"), Caret, Grp(Minus, s),
                Sp, Slash, Sp, F.Id("zeta"), Open, s, Close)),
            Seq(information),
            Seq(residual),
            Call("IndependentPrimeThermalSpectra", Call("zetaDist", s)),
            Seq(And(Call("ClassicallyCompletePrimeValuations"),
                Call("QuantumPhaseBlindPrimeDiagonals"))),
        ]);
        Formula premise = Seq(D(1), Sp, Lt, Sp, s);
        return Disp(new Formula.Logic(
            premise, FormulaLogicOperator.Implies, conclusion));
    }

    private static Formula BoundaryCounterexampleFormula()
    {
        Formula q = F.Id("q");
        Formula exists = Seq(
            Exists, Sp, q, Comma, Sp,
            Call("RealizesPrimeExponentLaw", D(1), q));
        return Disp(new Formula.Not(exists));
    }

    private static Formula Affinity(Formula p, Formula q) =>
        Call("countableHellingerAffinity", p, q);

    private static Formula Naturals() =>
        Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Primes() =>
        Seq(Mathbb, Grp(F.Id("P")));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
}
