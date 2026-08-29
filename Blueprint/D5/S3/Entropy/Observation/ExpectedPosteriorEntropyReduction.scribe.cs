using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Observation;

internal sealed class ExpectedPosteriorEntropyReductionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Entropy/Observation/ExpectedPosteriorEntropyReduction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite experiment information gain is exactly expected posterior entropy reduction.",
        H("Expected Posterior Entropy Reduction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("information-gain-equals-expected-entropy-reduction"),
                DeclarationHandle.Create(
                    Prefix + "information_gain_eq_expected_entropy_reduction"),
                H("Information gain equals expected posterior entropy reduction"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The state and observation carriers are finite. The induced joint "
                            + "weights are nonnegative, and each channel row has total mass "
                            + "one.")),
                    Paragraph(Text(
                        "The information gain is mutual information of the observation-first "
                            + "joint law. The posterior is the repository's totalized Bayes "
                            + "posterior, weighted by the output marginal.")),
                    Paragraph(Text(
                        "Prior normalization is not needed for this finite algebraic identity. "
                            + "Empty carriers and zero-probability output slices are included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("joint-nonnegativity-is-necessary"),
                DeclarationHandle.Create(Prefix + "joint_nonnegativity_is_necessary"),
                H("Joint nonnegativity is necessary"),
                StatementSource.FromAuthor(JointNonnegativityCounterexampleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A three-state signed prior with masses minus two, one, and one is "
                            + "observed through a normalized singleton-output channel.")),
                    Paragraph(Text(
                        "The induced joint has a negative cell and zero output mass. Under the "
                            + "repository's totalized logarithm and division conventions, the "
                            + "entropy-reduction identity fails."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("channel-normalization-is-necessary"),
                DeclarationHandle.Create(Prefix + "channel_normalization_is_necessary"),
                H("Channel normalization is necessary"),
                StatementSource.FromAuthor(ChannelNormalizationCounterexampleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A singleton prior of mass one and a singleton channel row of mass two "
                            + "give nonnegative induced joint weights.")),
                    Paragraph(Text(
                        "The row is not normalized, and its mutual information is nonzero under "
                            + "the repository definition while both displayed entropy terms "
                            + "vanish."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula RowSum(Formula channel, Formula state, Formula output) =>
        F.Seq(
            F.Sum,
            F.Underscore,
            F.Grp(output),
            F.Sp,
            Apply(channel, state, output));

    private static Formula RowNormalized(
        Formula channel,
        Formula stateType,
        Formula outputType)
    {
        Formula state = F.Id("x");
        Formula output = F.Id("y");
        return new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("x", stateType)],
            Equal(RowSum(channel, state, output), F.D(1)));
    }

    private static Formula JointNonnegative(
        Formula prior,
        Formula channel,
        Formula stateType,
        Formula outputType)
    {
        Formula state = F.Id("x");
        Formula output = F.Id("y");
        Formula cell = Multiply(Apply(prior, state), Apply(channel, state, output));
        return new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("y", outputType), Bound("x", stateType)],
            LessThanOrEqual(F.D(0), cell));
    }

    private static Formula EntropyIdentity(Formula prior, Formula channel) =>
        Equal(
            Call("informationGain", channel, prior),
            Subtract(
                Call("shannonEntropy", prior),
                Call("expectedPosteriorEntropy", channel, prior)));

    private static Formula MainFormula()
    {
        Formula type = F.Id("Type");
        Formula real = F.Id("Real");
        Formula stateType = F.Id("X");
        Formula outputType = F.Id("Y");
        Formula prior = F.Id("pi");
        Formula channel = F.Id("W");
        Formula finite = And(Call("Fintype", stateType), Call("Fintype", outputType));
        Formula assumptions = And(
            finite,
            And(
                JointNonnegative(prior, channel, stateType, outputType),
                RowNormalized(channel, stateType, outputType)));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", type),
                Bound("Y", type),
                Bound("pi", Arrow(stateType, real)),
                Bound("W", Arrow(stateType, Arrow(outputType, real))),
            ],
            new Formula.Logic(
                assumptions,
                FormulaLogicOperator.Implies,
                EntropyIdentity(prior, channel))));
    }

    private static Formula LetBinding(
        Formula name,
        Formula type,
        Formula value)
    {
        return F.Seq(
            F.Operatorname,
            F.Grp(F.Id("let")),
            F.Sp,
            name,
            F.Sp,
            F.Colon,
            F.Sp,
            type,
            F.Sp,
            F.Colon,
            F.Eq,
            F.Sp,
            value,
            F.Semi,
            F.RowBreak,
            F.Grp());
    }

    private static Formula JointNonnegativityCounterexampleFormula()
    {
        Formula real = F.Id("Real");
        Formula boolType = F.Id("Bool");
        Formula stateType = Call("Option", boolType);
        Formula outputType = F.Id("Unit");
        Formula prior = F.Id("pi");
        Formula channel = F.Id("W");
        Formula state = F.Id("x");
        Formula output = F.Id("y");
        Formula signedPrior = F.Seq(
            F.Open,
            state,
            F.Sp,
            F.Mapsto,
            F.Sp,
            Call(
                "if",
                Equal(state, F.Id("none")),
                new Formula.Negate(F.D(2)),
                F.D(1)),
            F.Close);
        Formula constantChannel = F.Seq(
            F.Open,
            state,
            F.Comma,
            F.Sp,
            output,
            F.Sp,
            F.Mapsto,
            F.Sp,
            F.D(1),
            F.Close);
        Formula priorLet = LetBinding(prior, Arrow(stateType, real), signedPrior);
        Formula channelLet = LetBinding(
            channel,
            Arrow(stateType, Arrow(outputType, real)),
            constantChannel);
        Formula conclusion = And(
            RowNormalized(channel, stateType, outputType),
            And(
                new Formula.Not(
                    JointNonnegative(prior, channel, stateType, outputType)),
                NotEqual(
                    Call("informationGain", channel, prior),
                    Subtract(
                        Call("shannonEntropy", prior),
                        Call("expectedPosteriorEntropy", channel, prior)))));

        return F.Disp(F.Seq(priorLet, channelLet, conclusion));
    }

    private static Formula ChannelNormalizationCounterexampleFormula()
    {
        Formula real = F.Id("Real");
        Formula unit = F.Id("Unit");
        Formula prior = F.Id("pi");
        Formula channel = F.Id("W");
        Formula state = F.Id("x");
        Formula output = F.Id("y");
        Formula unitPrior = F.Seq(
            F.Open,
            state,
            F.Sp,
            F.Mapsto,
            F.Sp,
            F.D(1),
            F.Close);
        Formula massTwoChannel = F.Seq(
            F.Open,
            state,
            F.Comma,
            F.Sp,
            output,
            F.Sp,
            F.Mapsto,
            F.Sp,
            F.D(2),
            F.Close);
        Formula priorLet = LetBinding(prior, Arrow(unit, real), unitPrior);
        Formula channelLet = LetBinding(
            channel,
            Arrow(unit, Arrow(unit, real)),
            massTwoChannel);
        Formula conclusion = And(
            JointNonnegative(prior, channel, unit, unit),
            And(
                new Formula.Not(RowNormalized(channel, unit, unit)),
                NotEqual(
                    Call("informationGain", channel, prior),
                    Subtract(
                        Call("shannonEntropy", prior),
                        Call("expectedPosteriorEntropy", channel, prior)))));

        return F.Disp(F.Seq(priorLet, channelLet, conclusion));
    }
}
