using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Sharpness;

internal sealed class FreeNegentropyBudgetDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Sharpness/FreeNegentropyBudget.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Density-state sharpness is controlled by negentropy, with monotone forgetting "
            + "and sharp endpoint laws.",
        H("The Free-Negentropy Budget"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ordered-density-state-spectrum"),
                DeclarationHandle.Create(Prefix + "stateSpectrum"),
                H("The ordered density-state spectrum"),
                StatementSource.FromAuthor(StateSpectrumFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The spectrum is constructed from the canonical density matrix by taking "
                        + "the decreasing real eigenvalue family of its positive-semidefinite "
                        + "Hermitian representative. It is not defined from any target bound."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("von-neumann-entropy-is-shannon-spectrum-entropy"),
                DeclarationHandle.Create(
                    Prefix + "von_neumann_entropy_eq_shannon_state_spectrum"),
                H("Von Neumann entropy is Shannon entropy of the ordered spectrum"),
                StatementSource.FromAuthor(EntropyBridgeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Finite-dimensional spectral calculus expands the trace-log definition "
                        + "over the density matrix eigenvalues. Reindexing those eigenvalues "
                        + "in decreasing order gives the stated Shannon entropy identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("free-negentropy-budget"),
                DeclarationHandle.Create(Prefix + "free_negentropy_budget"),
                H("Sharpness, forgetting, and endpoint budgets"),
                StatementSource.FromAuthor(BudgetFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a density state on a nonempty finite carrier, let r be its ordered "
                            + "spectrum and u the uniform spectrum. Spectral sharpness is the "
                            + "greatest bounded spectral pairing and is at most twice total "
                            + "variation from u, which Pinsker bounds by the square root of twice "
                            + "the von Neumann entropy deficit. Squaring gives the quantitative "
                            + "free-negentropy budget.")),
                    Paragraph(Text(
                        "A supplied doubly stochastic spectral mixing witness models forgetting. "
                            + "It decreases sharpness and every antitone pairing capacity, increases "
                            + "Shannon entropy, and therefore decreases the entropy deficit.")),
                    Paragraph(Text(
                        "The canonical symmetric two-point law realizes the qubit endpoint. Its "
                            + "sharpness and twice-total-variation are the radius, the Pinsker ratio "
                            + "tends to one at the mixed endpoint, and the fourth-order residual has "
                            + "coefficient one sixth with a sixth-order remainder. At sharpness one, "
                            + "the density-matrix rank is at most half the dimension and controls "
                            + "the remaining entropy.")),
                    Paragraph(Text(
                        "The source's random-spectrum trial count, floating-point alert review, "
                            + "and seven-digit numerical comparison are empirical certificate "
                            + "remarks outside the named theorem. The exact inequalities, limit, "
                            + "expansion, and rank endpoint are the formalized clauses."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(hypothesis, FormulaLogicOperator.Implies, conclusion);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Divide(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(name),
            domain,
            body);

    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create(name),
            domain,
            body);

    private static Formula Lambda(Formula binder, Formula domain, Formula body) =>
        Seq(Open, binder, Colon, Sp, domain, Sp, Mapsto, Sp, body, Close);

    private static Formula LetDefinition(Formula name, Formula type, Formula value) =>
        Seq(
            Operatorname, Grp(F.Id("let")), Sp, name, Colon, Sp, type,
            Sp, Colon, Eq, Sp, value, Semi, Sp);

    private static Formula Gathered(params Formula[] clauses)
    {
        var items = new List<Formula> { Begin, Grp(F.Id("gathered")) };
        for (var index = 0; index < clauses.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Sp);
                items.Add(Land);
                items.Add(RowBreak);
                items.Add(Grp());
            }

            items.Add(clauses[index]);
        }

        items.Add(Dot);
        items.Add(End);
        items.Add(Grp(F.Id("gathered")));
        return Seq([.. items]);
    }

    private static Formula StateSpectrumFormula()
    {
        Formula carrier = F.Id("n"), state = Rho;
        Formula type = F.Id("Type");
        Formula density = Call("DensityState", carrier);
        Formula assumptions = And(Call("Fintype", carrier), Call("DecidableEq", carrier));
        Formula eigenvalues = new Formula.Subscript(F.Id("eigenvalues"), D(0));
        Formula construction = Equal(
            Call("stateSpectrum", state),
            Apply(eigenvalues, Call("densityMatrix", state)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("n", type), Bound("rho", density)],
            Implies(assumptions, construction)));
    }

    private static Formula EntropyBridgeFormula()
    {
        Formula carrier = F.Id("n"), state = Rho;
        Formula type = F.Id("Type");
        Formula density = Call("DensityState", carrier);
        Formula assumptions = And(Call("Fintype", carrier), Call("DecidableEq", carrier));
        Formula identity = Equal(
            Call("vonNeumannEntropy", state),
            Call("shannonEntropy", Call("stateSpectrum", state)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("n", type), Bound("rho", density)],
            Implies(assumptions, identity)));
    }

    private static Formula BudgetFormula()
    {
        Formula carrier = F.Id("n"), state = Rho, sigma = F.Id("sigma");
        Formula index = F.Id("i"), observable = F.Id("a"), value = F.Id("v");
        Formula mixing = F.Id("S"), radius = F.Id("x");
        Formula spectrum = F.Id("r"), uniform = F.Id("u"), qubit = F.Id("q");
        Formula type = F.Id("Type"), real = Seq(Mathbb, Grp(F.Id("R")));
        Formula cardinality = Call("card", carrier);
        Formula spectrumIndex = Call("Fin", cardinality);
        Formula finTwo = Call("Fin", D(2));
        Formula spectrumType = Arrow(spectrumIndex, real);
        Formula qubitType = Arrow(real, Arrow(finTwo, real));
        Formula density = Call("DensityState", carrier);
        Formula matrix = Call("Matrix", spectrumIndex, spectrumIndex, real);

        Formula At(Formula function, Formula argument) => Apply(function, argument);
        Formula Spec(Formula densityState) => Call("stateSpectrum", densityState);
        Formula Sharp(Formula law) => Call("spectralSharpness", law);
        Formula Entropy(Formula law) => Call("shannonEntropy", law);
        Formula VonNeumann(Formula densityState) => Call("vonNeumannEntropy", densityState);
        Formula Variation(Formula left, Formula right) =>
            Call("totalVariation", left, right);
        Formula Capacity(Formula law, Formula test) =>
            Call("spectralPairingCapacity", law, test);
        Formula Twice(Formula expression) => Multiply(D(2), expression);
        Formula Square(Formula expression) => Power(expression, D(2));
        Formula Log(Formula expression) => Call("log", expression);
        Formula Deficit(Formula law) => Subtract(Log(cardinality), Entropy(law));
        Formula SumOver(Formula law, Formula domain) =>
            Seq(Sum, Underscore, Grp(index, Sp, InMacro, Sp, domain), Sp, At(law, index));

        Formula instanceAssumptions = And(
            Call("Fintype", carrier),
            And(Call("DecidableEq", carrier), Call("Nonempty", carrier)));
        Formula stateSpectrumDefinition = LetDefinition(
            spectrum, spectrumType, Spec(state));
        Formula uniformDefinition = LetDefinition(
            uniform,
            spectrumType,
            Lambda(index, spectrumIndex, Divide(D(1), cardinality)));
        Formula qubitAt = Call(
            "ite",
            Equal(index, D(0)),
            Add(Divide(D(1), D(2)), Divide(radius, D(2))),
            Subtract(Divide(D(1), D(2)), Divide(radius, D(2))));
        Formula qubitDefinition = LetDefinition(
            qubit,
            qubitType,
            Lambda(radius, real, Lambda(index, finTwo, qubitAt)));

        Formula probability = And(
            ForAll("i", spectrumIndex, LessOrEqual(D(0), At(spectrum, index))),
            Equal(SumOver(spectrum, spectrumIndex), D(1)));
        Formula antitone = Call("Antitone", spectrum);
        Formula entropyBridge = Equal(VonNeumann(state), Entropy(spectrum));

        Formula observableType = Arrow(spectrumIndex, real);
        Formula boundedObservable = ForAll(
            "i",
            spectrumIndex,
            LessOrEqual(new Formula.Absolute(At(observable, index)), D(1)));
        Formula attainedValue = Exists(
            "a",
            observableType,
            And(boundedObservable, Equal(Capacity(spectrum, observable), value)));
        Formula pairingValues = Seq(
            OpenBrace, value, Colon, Sp, real, Sp, Mid, Sp, attainedValue, CloseBrace);
        Formula variationalSharpness =
            Call("IsGreatest", pairingValues, Sharp(spectrum));

        Formula twiceVariation = Twice(Variation(spectrum, uniform));
        Formula entropyRadicand = Twice(Subtract(Log(cardinality), VonNeumann(state)));
        Formula budget = And(
            LessOrEqual(Sharp(spectrum), twiceVariation),
            LessOrEqual(twiceVariation, Call("sqrt", entropyRadicand)));
        Formula squaredBudget = LessOrEqual(Square(Sharp(spectrum)), entropyRadicand);

        Formula sigmaSpectrum = Spec(sigma);
        Formula mixingAssumptions = And(
            Call("doublyStochastic", mixing),
            Equal(spectrum, Call("mulVec", mixing, sigmaSpectrum)));
        Formula everyCapacity = ForAll(
            "a",
            observableType,
            Implies(
                Call("Antitone", observable),
                LessOrEqual(
                    Capacity(spectrum, observable),
                    Capacity(sigmaSpectrum, observable))));
        Formula mixingConclusion = Gathered(
            LessOrEqual(Sharp(spectrum), Sharp(sigmaSpectrum)),
            LessOrEqual(Entropy(sigmaSpectrum), Entropy(spectrum)),
            LessOrEqual(Deficit(spectrum), Deficit(sigmaSpectrum)),
            everyCapacity);
        Formula forgetting = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("sigma", density), Bound("S", matrix)],
            Implies(mixingAssumptions, mixingConclusion));

        Formula qubitLaw = Apply(qubit, radius);
        Formula biasLaw = Call("positiveBiasLaw", Divide(radius, D(2)));
        Formula qubitProbability = And(
            ForAll("i", finTwo, LessOrEqual(D(0), At(qubitLaw, index))),
            Equal(SumOver(qubitLaw, finTwo), D(1)));
        Formula qubitEndpoint = ForAll(
            "x",
            real,
            Implies(
                And(LessOrEqual(D(0), radius), LessOrEqual(radius, D(1))),
                Gathered(
                    qubitProbability,
                    Call("Antitone", qubitLaw),
                    Equal(Entropy(qubitLaw), Entropy(biasLaw)),
                    Equal(Sharp(qubitLaw), radius),
                    Equal(
                        Twice(Variation(biasLaw, Call("positiveBiasLaw", D(0)))),
                        radius))));

        Formula qubitDeficit = Subtract(Log(D(2)), Entropy(biasLaw));
        Formula ratio = Divide(
            Twice(Variation(biasLaw, Call("positiveBiasLaw", D(0)))),
            Call("sqrt", Twice(qubitDeficit)));
        Formula firstOrder = Call(
            "Tendsto",
            Lambda(radius, real, ratio),
            Call("nhdsWithin", D(0), Call("Ioi", D(0))),
            Call("nhds", D(1)));

        Formula fourthRemainder = Subtract(
            Subtract(Twice(qubitDeficit), Square(Twice(
                Variation(biasLaw, Call("positiveBiasLaw", D(0)))))),
            Divide(Power(radius, D(4)), D(6)));
        Formula fourthOrder = Call(
            "IsBigO",
            Lambda(radius, real, fourthRemainder),
            Call("nhds", D(0)),
            Lambda(radius, real, Power(radius, D(6))));

        Formula rank = Call("rank", Call("densityMatrix", state));
        Formula halfCardinality = new Formula.Floor(Divide(cardinality, D(2)));
        Formula saturated = Implies(
            Equal(Sharp(spectrum), D(1)),
            Gathered(
                LessOrEqual(rank, halfCardinality),
                LessOrEqual(VonNeumann(state), Log(rank)),
                LessOrEqual(VonNeumann(state), Log(halfCardinality))));

        Formula conclusion = Seq(
            stateSpectrumDefinition, RowBreak, Grp(),
            uniformDefinition, RowBreak, Grp(),
            qubitDefinition, RowBreak, Grp(),
            Gathered(
                probability,
                antitone,
                entropyBridge,
                variationalSharpness,
                budget,
                squaredBudget,
                forgetting,
                qubitEndpoint,
                firstOrder,
                fourthOrder,
                Grp(saturated)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("n", type), Bound("rho", density)],
            Implies(instanceAssumptions, conclusion)));
    }
}
