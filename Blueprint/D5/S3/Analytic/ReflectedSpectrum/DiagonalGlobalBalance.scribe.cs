using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ReflectedSpectrum;

internal sealed class DiagonalGlobalBalanceDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/ReflectedSpectrum/DiagonalGlobalBalance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A single shared orientation bit centers every orbit while preserving maximal pairwise direction correlation.",
        H("Diagonal Global Balance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("diagonal-law"),
                DeclarationHandle.Create(Prefix + "diagonalLaw"),
                H("The global diagonal reflection law"),
                StatementSource.FromAuthor(DiagonalLawFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The uniform binary orientation bit is sent to the corresponding constant "
                        + "configuration. Its pushforward is exactly the half-half law on the "
                        + "all-negative and all-positive configurations of the finite window."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("diagonal-law-is-probability-measure"),
                DeclarationHandle.Create(Prefix + "diagonalLaw_isProbabilityMeasure"),
                H("The diagonal law is a probability measure"),
                StatementSource.FromAuthor(DiagonalLawProbabilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Mapping the uniform probability mass function on the two orientation bits "
                        + "preserves total mass one."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("orbit-readout"),
                DeclarationHandle.Create(Prefix + "orbitReadout"),
                H("Signed displacement at one orbit"),
                StatementSource.FromAuthor(OrbitReadoutFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The readout multiplies the binary coordinate sign by the real displacement "
                        + "attached to the selected orbit."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("diagonal-joint-second-moment"),
                DeclarationHandle.Create(Prefix + "diagonal_joint_second_moment"),
                H("Joint second moment under the shared bit"),
                StatementSource.FromAuthor(JointSecondMomentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Both readouts see the same orientation bit, whose square is one. The exact "
                        + "joint second moment is therefore the product of the two displacements."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("diagonal-global-balance"),
                DeclarationHandle.Create(Prefix + "diagonal_global_balance"),
                H("Local balance and global maximal correlation"),
                StatementSource.FromAuthor(GlobalBalanceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every finite orbit type and every real displacement family, each "
                            + "orbit readout has expectation zero under the diagonal law. Distinct "
                            + "orbit readouts have covariance equal to the product of their "
                            + "displacements.")),
                    Paragraph(Text(
                        "The squared covariance equals the product of the two variances, which "
                            + "records saturation of the covariance-variance bound and hence "
                            + "maximal absolute direction correlation.")),
                    Paragraph(Text(
                        "If the displacement product of a distinct pair is nonzero, the coordinate "
                            + "projections cannot be jointly independent. Hypothetical coordinate "
                            + "independence would pass through the signed-displacement maps and "
                            + "force their nonzero covariance to vanish."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Analytic/ReflectedSpectrum/ParityConditionedMoments"))]));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula ForallFormula(Formula.BoundVariable[] binders, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. binders], body);

    private static Formula Lambda(string name, Formula domain, Formula body) =>
        Seq(Open, F.Id(name), Colon, Sp, domain, Sp, Mapsto, Sp, body, Close);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula RealType() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula UniverseType() => Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula FinTwo() => Call("Fin", D(2));

    private static Formula ConfigurationType(Formula orbitType) =>
        Arrow(orbitType, FinTwo());

    private static Formula Law(Formula orbitType) => Call("diagonalLaw", orbitType);

    private static Formula Readout(
        Formula delta,
        Formula orbit,
        Formula configuration) =>
        Call("orbitReadout", delta, orbit, configuration);

    private static Formula Integral(
        Formula orbitType,
        Formula configuration,
        Formula integrand) =>
        Call(
            "integral",
            Lambda("configuration", ConfigurationType(orbitType), integrand),
            Law(orbitType));

    private static Formula DiagonalLawFormula()
    {
        Formula type = UniverseType();
        Formula orbitType = F.Id("T");
        Formula bit = F.Id("bit");
        Formula constantConfiguration = Lambda(
            "bit",
            FinTwo(),
            Lambda("index", orbitType, bit));
        Formula pushforward = Call(
            "map",
            Call("uniformOfFintype", FinTwo()),
            constantConfiguration);
        Formula definition = Equal(
            Law(orbitType),
            Call("toMeasure", pushforward));

        return Disp(Seq(
            ForallFormula(
                [Bound("T", type)],
                Implies(Call("Fintype", orbitType), definition)),
            Dot));
    }

    private static Formula OrbitReadoutFormula()
    {
        Formula type = UniverseType();
        Formula real = RealType();
        Formula orbitType = F.Id("T");
        Formula delta = F.Id("delta");
        Formula orbit = F.Id("orbit");
        Formula configuration = F.Id("configuration");
        Formula sign = Call(
            "real",
            Call("paritySign", Apply(configuration, orbit)));
        Formula definition = Equal(
            Readout(delta, orbit, configuration),
            Multiply(sign, Apply(delta, orbit)));

        return Disp(Seq(
            ForallFormula(
                [
                    Bound("T", type),
                    Bound("delta", Arrow(orbitType, real)),
                    Bound("orbit", orbitType),
                    Bound("configuration", ConfigurationType(orbitType)),
                ],
                definition),
            Dot));
    }

    private static Formula DiagonalLawProbabilityFormula()
    {
        Formula type = UniverseType();
        Formula orbitType = F.Id("T");
        Formula result = Call("IsProbabilityMeasure", Law(orbitType));

        return Disp(Seq(
            ForallFormula(
                [Bound("T", type)],
                Implies(Call("Fintype", orbitType), result)),
            Dot));
    }

    private static Formula JointSecondMomentFormula()
    {
        Formula type = UniverseType();
        Formula real = RealType();
        Formula orbitType = F.Id("T");
        Formula delta = F.Id("delta");
        Formula orbit = F.Id("orbit");
        Formula orbitPrime = F.Id("orbitPrime");
        Formula configuration = F.Id("configuration");
        Formula integrand = Multiply(
            Readout(delta, orbit, configuration),
            Readout(delta, orbitPrime, configuration));
        Formula result = Equal(
            Integral(orbitType, configuration, integrand),
            Multiply(Apply(delta, orbit), Apply(delta, orbitPrime)));

        return Disp(Seq(
            ForallFormula(
                [
                    Bound("T", type),
                    Bound("delta", Arrow(orbitType, real)),
                    Bound("orbit", orbitType),
                    Bound("orbitPrime", orbitType),
                ],
                Implies(Call("Fintype", orbitType), result)),
            Dot));
    }

    private static Formula GlobalBalanceFormula()
    {
        Formula type = UniverseType();
        Formula real = RealType();
        Formula orbitType = F.Id("T");
        Formula delta = F.Id("delta");
        Formula orbit = F.Id("orbit");
        Formula orbitPrime = F.Id("orbitPrime");
        Formula configuration = F.Id("configuration");
        Formula readout = Lambda(
            "configuration",
            ConfigurationType(orbitType),
            Readout(delta, orbit, configuration));
        Formula readoutPrime = Lambda(
            "configuration",
            ConfigurationType(orbitType),
            Readout(delta, orbitPrime, configuration));
        Formula deltaProduct = Multiply(Apply(delta, orbit), Apply(delta, orbitPrime));
        Formula covariance = Call("covariance", readout, readoutPrime, Law(orbitType));
        Formula variance = Call("variance", readout, Law(orbitType));
        Formula variancePrime = Call("variance", readoutPrime, Law(orbitType));
        Formula projections = Lambda(
            "index",
            orbitType,
            Lambda(
                "configuration",
                ConfigurationType(orbitType),
                Apply(configuration, F.Id("index"))));
        Formula centered = ForallFormula(
            [Bound("orbit", orbitType)],
            Equal(
                Integral(
                    orbitType,
                    configuration,
                    Readout(delta, orbit, configuration)),
                D(0)));
        Formula pairConclusion = And(
            Equal(covariance, deltaProduct),
            And(
                Equal(
                    new Formula.Power(covariance, D(2)),
                    Multiply(variance, variancePrime)),
                Implies(
                    NotEqual(deltaProduct, D(0)),
                    new Formula.Not(Call("iIndepFun", projections, Law(orbitType))))));
        Formula distinctPairs = ForallFormula(
            [Bound("orbit", orbitType), Bound("orbitPrime", orbitType)],
            Implies(NotEqual(orbit, orbitPrime), pairConclusion));
        Formula conclusion = And(centered, distinctPairs);

        return Disp(Seq(
            ForallFormula(
                [Bound("T", type), Bound("delta", Arrow(orbitType, real))],
                Implies(Call("Fintype", orbitType), conclusion)),
            Dot));
    }
}
