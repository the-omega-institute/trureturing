using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.CountableSlices;

internal sealed class SinglePrimeThermalStateDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/CountableSlices/SinglePrimeThermalState.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The single-prime thermal spectrum is a normalized geometric occupation law.",
        H("Single-Prime Thermal State"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("single-prime-thermal-spectrum"),
                DeclarationHandle.Create(Prefix + "singlePrimeThermalState"),
                H("Single-prime thermal spectrum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The countable diagonal model is represented by the occupation-number " +
                    "spectrum (1 - p^(-s)) p^(-s k) at mode k."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("single-prime-thermal-pmf"),
                DeclarationHandle.Create(Prefix + "singlePrimeThermalPMF"),
                H("PMF associated with the thermal spectrum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In the regime p > 1 and s > 0, the spectrum is packaged as a countable " +
                    "probability mass function."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("single-prime-thermal-spectrum-nonnegative"),
                DeclarationHandle.Create(Prefix + "singlePrimeThermalState_nonneg"),
                H("Thermal spectral weights are nonnegative"),
                StatementSource.FromAuthor(NonnegativeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For p > 1 and s > 0, the ratio p^(-s) lies in (0, 1). Both factors in " +
                    "each diagonal weight are therefore nonnegative."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("single-prime-thermal-spectrum-normalized"),
                DeclarationHandle.Create(Prefix + "singlePrimeThermalState_tsum_eq_one"),
                H("Thermal spectral weights are normalized"),
                StatementSource.FromAuthor(NormalizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The geometric series with ratio p^(-s) sums to the inverse prefactor, " +
                    "so the diagonal spectrum has total mass one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("single-prime-thermal-zero-slot"),
                DeclarationHandle.Create(Prefix + "singlePrimeThermalState_zero_slot"),
                H("The zero occupation slot"),
                StatementSource.FromAuthor(ZeroSlotFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At k = 0 the geometric power is one, leaving exactly the vacuum " +
                    "weight 1 - p^(-s)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("single-prime-thermal-pmf-apply"),
                DeclarationHandle.Create(Prefix + "singlePrimeThermalPMF_apply"),
                H("The PMF realizes the thermal spectrum"),
                StatementSource.FromAuthor(PmfApplyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Taking the real mass of the named PMF recovers the corresponding " +
                    "diagonal spectral weight at every occupation number."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("single-prime-thermal-pmf-geometric"),
                DeclarationHandle.Create(Prefix + "singlePrimeThermalPMF_is_geometric"),
                H("The PMF is geometric in the ratio parameter"),
                StatementSource.FromAuthor(GeometricFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The PMF has geometric ratio p^(-s), with success prefactor " +
                    "1 - p^(-s), pointwise on the countable occupation space."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("single-prime-thermal-entropy"),
                DeclarationHandle.Create(Prefix + "singlePrimeThermal_entropy_eq"),
                H("Closed entropy of one thermal mode"),
                StatementSource.FromAuthor(EntropyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The reusable geometric Gibbs entropy theorem gives the closed Shannon " +
                    "formula for this diagonal mode; only p > 1 and s > 0 are needed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("modal-thermal-entropy-additivity"),
                DeclarationHandle.Create(Prefix + "modal_thermal_entropy_additive"),
                H("Modal thermal entropy adds over primes"),
                StatementSource.FromAuthor(AdditivityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For s > 1, the existing zeta diagonal PMF entropy equals the tsum of " +
                    "the named single-prime thermal mode entropies."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("base-gt-one-is-necessary"),
                DeclarationHandle.Create(Prefix + "base_gt_one_is_necessary"),
                H("Base greater than one is necessary"),
                StatementSource.FromAuthor(BaseCounterexampleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At the concrete base p = 1 and s = 1, every prefactor is zero and " +
                    "normalization fails."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-temperature-is-necessary"),
                DeclarationHandle.Create(Prefix + "positive_temperature_is_necessary"),
                H("Positive temperature is necessary"),
                StatementSource.FromAuthor(TemperatureCounterexampleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At the concrete base p = 2 and temperature s = 0, the ratio is one, " +
                    "all weights vanish, and the total is not one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("negative-temperature-is-not-summable"),
                DeclarationHandle.Create(Prefix + "negative_temperature_not_summable"),
                H("A negative-temperature spectrum is not summable"),
                StatementSource.FromAuthor(NegativeTemperatureFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At p = 2 and s = -1, the weights are -2^k, giving a concrete " +
                    "non-summable divergent boundary case."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("thermal-spectrum-vacuum-limit"),
                DeclarationHandle.Create(
                    Prefix + "singlePrimeThermalState_tendsto_infinite_temperature"),
                H("Infinite temperature leaves the vacuum spectrum"),
                StatementSource.FromAuthor(VacuumLimitFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a fixed occupation number and p > 1, the spectrum tends as s tends " +
                    "to infinity to one at k = 0 and zero at every k > 0."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        return new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    }

    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Hypotheses(Formula p, Formula s) =>
        And(Rel(D(1), FormulaRelationOperator.LessThan, p),
            Rel(D(0), FormulaRelationOperator.LessThan, s));

    private static Formula State(Formula p, Formula s, Formula k) =>
        Call("singlePrimeThermalState", p, s, k);

    private static Formula Pmf(Formula p, Formula s) =>
        Call("singlePrimeThermalPMF", p, s);

    private static Formula Entropy(Formula p, Formula s) =>
        Call("countableEntropy", Pmf(p, s));

    private static Formula Ratio(Formula p, Formula s) =>
        new Formula.Power(p, F.Grp(F.Minus, s));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Naturals() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("N")));

    private static Formula Reals() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("R")));

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula NonnegativeFormula()
    {
        Formula p = F.Id("p");
        Formula s = F.Id("s");
        Formula k = F.Id("k");
        return Disp(ForAll(
            [Bound("p", Naturals()), Bound("s", Reals()), Bound("k", Naturals())],
            new Formula.Logic(Hypotheses(p, s), FormulaLogicOperator.Implies,
                Rel(D(0), FormulaRelationOperator.LessThanOrEqual, State(p, s, k)))));
    }

    private static Formula NormalizationFormula()
    {
        Formula p = F.Id("p");
        Formula s = F.Id("s");
        Formula sum = Call("tsum", F.Id("k"), State(p, s, F.Id("k")));
        return Disp(ForAll(
            [Bound("p", Naturals()), Bound("s", Reals())],
            new Formula.Logic(Hypotheses(p, s), FormulaLogicOperator.Implies,
                Rel(sum, FormulaRelationOperator.Equal, D(1)))));
    }

    private static Formula ZeroSlotFormula() =>
        Disp(Rel(State(F.Id("p"), F.Id("s"), D(0)), FormulaRelationOperator.Equal,
            F.Seq(D(1), Sp, Minus, Sp, Ratio(F.Id("p"), F.Id("s")))));

    private static Formula PmfApplyFormula()
    {
        Formula p = F.Id("p");
        Formula s = F.Id("s");
        Formula k = F.Id("k");
        Formula left = Call("pmfReal", Pmf(p, s), k);
        return Disp(ForAll(
            [Bound("p", Naturals()), Bound("s", Reals()), Bound("k", Naturals())],
            new Formula.Logic(Hypotheses(p, s), FormulaLogicOperator.Implies,
                Rel(left, FormulaRelationOperator.Equal, State(p, s, k)))));
    }

    private static Formula GeometricFormula()
    {
        Formula p = F.Id("p");
        Formula s = F.Id("s");
        Formula k = F.Id("k");
        Formula left = Call("pmfReal", Pmf(p, s), k);
        Formula right = F.Seq(
            Open, D(1), Sp, Minus, Sp, Ratio(p, s), Close, Sp,
            Call("pow", Ratio(p, s), k));
        return Disp(ForAll(
            [Bound("p", Naturals()), Bound("s", Reals()), Bound("k", Naturals())],
            new Formula.Logic(Hypotheses(p, s), FormulaLogicOperator.Implies,
                Rel(left, FormulaRelationOperator.Equal, right))));
    }

    private static Formula EntropyFormula()
    {
        Formula p = F.Id("p");
        Formula s = F.Id("s");
        Formula q = Ratio(p, s);
        Formula right = F.Seq(
            Minus, Log(F.Seq(D(1), Sp, Minus, Sp, q)), Sp, Plus, Sp,
            s, Sp, Log(p), Sp, F.Seq(q, Sp, Slash, Sp,
                F.Seq(D(1), Sp, Minus, Sp, q)));
        return Disp(ForAll(
            [Bound("p", Naturals()), Bound("s", Reals())],
            new Formula.Logic(Hypotheses(p, s), FormulaLogicOperator.Implies,
                Rel(Entropy(p, s), FormulaRelationOperator.Equal, right))));
    }

    private static Formula AdditivityFormula()
    {
        Formula s = F.Id("s");
        Formula prime = F.Id("p");
        Formula sum = Call("tsum", F.Id("p"), Entropy(prime, s));
        return Disp(ForAll(
            [Bound("s", Reals())],
            new Formula.Logic(Rel(D(1), FormulaRelationOperator.LessThan, s),
                FormulaLogicOperator.Implies,
                Rel(Call("countableEntropy", Call("zetaDist", s)),
                    FormulaRelationOperator.Equal, sum))));
    }

    private static Formula BaseCounterexampleFormula() =>
        Disp(new Formula.Not(Rel(Call("tsum", F.Id("k"),
            State(D(1), D(1), F.Id("k"))), FormulaRelationOperator.Equal, D(1))));

    private static Formula TemperatureCounterexampleFormula() =>
        Disp(new Formula.Not(Rel(Call("tsum", F.Id("k"),
            State(D(2), D(0), F.Id("k"))), FormulaRelationOperator.Equal, D(1))));

    private static Formula NegativeTemperatureFormula() =>
        Disp(new Formula.Not(Call("Summable", Call("singlePrimeThermalState", D(2),
            F.Seq(Minus, D(1))))));

    private static Formula VacuumLimitFormula()
    {
        Formula p = F.Id("p");
        Formula k = F.Id("k");
        Formula limit = Call("Tendsto", Call("singlePrimeThermalState", p, F.Id("s"), k),
            F.Id("atTop"), Call("nhds", Call("if", Rel(k, FormulaRelationOperator.Equal, D(0)),
                D(1), D(0))));
        return Disp(ForAll(
            [Bound("p", Naturals()), Bound("k", Naturals())],
            new Formula.Logic(Rel(D(1), FormulaRelationOperator.LessThan, p),
                FormulaLogicOperator.Implies, limit)));
    }

    private static Formula Log(Formula value) => Call("log", value);
}
