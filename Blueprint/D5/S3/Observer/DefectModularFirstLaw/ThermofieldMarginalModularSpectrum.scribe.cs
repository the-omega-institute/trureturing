using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.DefectModularFirstLaw;

internal sealed class ThermofieldMarginalModularSpectrumDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/DefectModularFirstLaw/ThermofieldMarginalModularSpectrum.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The countable thermofield state reduces to the geometric thermal law whose entropy "
            + "derivative and relative modular level spacing coincide.",
        H("Thermofield Marginal and Modular Spectrum"),
        Blocks(
            Definition(
                "thermofield-amplitude",
                "The countable thermofield amplitude",
                "thermofieldAmplitude",
                "The amplitude is supported on matching visible and hidden occupations, with "
                    + "Schmidt coefficient sqrt((1-q)q^n)."),
            Definition(
                "countable-partial-trace-right",
                "Partial trace over the hidden mode",
                "countablePartialTraceRight",
                "The hidden countable coordinate is traced out by summing the corresponding "
                    + "diagonal blocks."),
            Definition(
                "geometric-diagonal-density",
                "The visible geometric density",
                "geometricDiagonalDensity",
                "The visible occupation n has diagonal weight (1-q)q^n."),
            Definition(
                "diagonal-entropy",
                "Entropy of a countable diagonal density",
                "diagonalEntropy",
                "The entropy is the infinite sum of -p log p over the real diagonal weights."),
            Definition(
                "relative-modular-energy",
                "Relative modular energy levels",
                "relativeModularEnergy",
                "The n-th modular energy is minus the logarithm of the n-th visible density "
                    + "eigenvalue."),
            Describe.Lean(
                DescribeId.Create("local-modular-first-law-from-thermofield-marginal"),
                DeclarationHandle.Create(
                    Prefix + "local_modular_first_law_from_thermofield_marginal"),
                H("The local modular first law on the thermofield marginal"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For real scales 0 < omega < delta, q is (omega/delta)^2, N is the "
                            + "visible geometric occupation, and epsilon is the defect modular "
                            + "gap 2 log(delta/omega).")),
                    Paragraph(Text(
                        "The frozen derivative theorem supplies the differential law. The new "
                            + "countable Schmidt construction proves that tracing out the hidden "
                            + "mode from the frozen generic rank-one density gives the normalized "
                            + "geometric density, whose first moment is N and whose diagonal entropy "
                            + "is exactly S(N).")),
                    Paragraph(Text(
                        "The negative logarithms of successive visible eigenweights differ by "
                            + "epsilon, so epsilon is the adjacent level spacing of the relative "
                            + "modular Hamiltonian. This states only local rank-one modular "
                            + "thermodynamics, not a physical black-hole first law."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(
        string id,
        string title,
        string declaration,
        string commentary) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(commentary))),
            DescribeRole.Definition);

    private static Formula TheoremFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula delta = F.Id("delta");
        Formula omega = F.Id("omega");
        Formula q = F.Id("q");
        Formula occupation = F.Id("N");
        Formula epsilon = F.Id("epsilon");
        Formula visibleDensity = new Formula.Subscript(Rho, F.Id("vis"));
        Formula dN = F.Id("dN");
        Formula n = F.Id("n");

        Formula qValue = new Formula.Power(
            Grp(new Formula.Fraction(omega, delta)),
            D(2));
        Formula occupationValue = Call(
            "rankOneThermalOccupation",
            q);
        Formula epsilonValue = Call("defectModularGap", delta, omega);
        Formula visibleValue = Call(
            "countablePartialTraceRight",
            Call(
                "rankOneDensity",
                Call("thermofieldAmplitude", q)));
        Formula entropy = F.Id("rankOneThermalEntropy");
        Formula logRatio = Logarithm(new Formula.Fraction(
            Seq(occupation, Sp, Plus, Sp, D(1)),
            occupation));
        Formula minusLogQ = Seq(Minus, Logarithm(q));

        Formula derivativeClauses = All(
            Call("HasDerivAt", entropy, logRatio, occupation),
            Equal(logRatio, minusLogQ),
            Equal(minusLogQ, epsilon));
        Formula differentialClause = ForAll(
            [Bound("dN", real)],
            Equal(
                Apply(Call("fderiv", real, entropy, occupation), dN),
                Seq(epsilon, Sp, dN)));
        Formula explicitGap = Equal(
            epsilon,
            Seq(D(2), Sp, Logarithm(new Formula.Fraction(delta, omega))));
        Formula marginalClause = Equal(
            visibleDensity,
            Call("geometricDiagonalDensity", q));
        Formula normalizationClause = Equal(
            Call(
                "tsum",
                Lambda(
                    Typed(n, natural),
                    Call("re", Apply(visibleDensity, n, n)))),
            D(1));
        Formula meanOccupationClause = Equal(
            Call(
                "tsum",
                Lambda(
                    Typed(n, natural),
                    Seq(
                        Open,
                        Typed(n, real),
                        Close,
                        Sp,
                        Call("re", Apply(visibleDensity, n, n))))),
            occupation);
        Formula entropyClause = Equal(
            Call("diagonalEntropy", visibleDensity),
            Call("rankOneThermalEntropy", occupation));
        Formula energy = Call("relativeModularEnergy", q, n);
        Formula nextEnergy = Call(
            "relativeModularEnergy",
            q,
            Seq(n, Sp, Plus, Sp, D(1)));
        Formula spacingClause = ForAll(
            [Bound("n", natural)],
            Equal(Seq(nextEnergy, Sp, Minus, Sp, energy), epsilon));

        Formula assumptions = And(
            Less(D(0), omega),
            Less(omega, delta));
        Formula conclusions = All(
            derivativeClauses,
            And(differentialClause, explicitGap),
            marginalClause,
            normalizationClause,
            meanOccupationClause,
            entropyClause,
            spacingClause);

        return Disp(ForAll(
            [Bound("delta", real), Bound("omega", real)],
            Implies(
                assumptions,
                Seq(
                    Let(q, real, qValue),
                    Let(occupation, real, occupationValue),
                    Let(epsilon, real, epsilonValue),
                    Let(
                        visibleDensity,
                        Call("Matrix", natural, natural, Seq(Mathbb, Grp(F.Id("C")))),
                        visibleValue),
                    conclusions))));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
        {
            result = And(clauses[index], result);
        }

        return result;
    }

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Typed(Formula variable, Formula type) =>
        Seq(variable, Colon, Sp, type);

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula Let(Formula name, Formula type, Formula value) =>
        Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            name, Colon, Sp, type, Sp, Eq, Sp, value, Comma, Sp);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Logarithm(Formula argument) =>
        Seq(Log, Sp, Open, argument, Close);
}
