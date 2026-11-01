using System.Text.Json;
using System.Collections.Immutable;
using StrataLint.Engine;
using Xunit;

namespace StrataLint.Scribe.Tests;

public sealed class StatementProjectionExpansionTests
{
    public static IEnumerable<object[]> ExpansionPins()
    {
        using var fixture = JsonDocument.Parse(RepositoryAccessor.Discover(
            RepositoryRootCriterion.LakefileInvalidOperation).ReadAllBytes(
                RepositoryRelativePath.Create("Golden/Projection/statement-projection-expansion-v1.json")));
        foreach (var declaration in fixture.RootElement.GetProperty("declarations").EnumerateArray())
            yield return [declaration.GetProperty("name").GetString()!, declaration.GetProperty("type").GetString()!];
    }

    [Theory]
    [MemberData(nameof(ExpansionPins))]
    public void ExpansionPinProjectsWithNamedDiagnostic(string name, string type)
    {
        var outcome = StatementProjector.Project(StatementV1Decoder.Decode(type).Type);
        Assert.True(outcome is ProjectionOutcome.Projected,
            name + ": " + (outcome as ProjectionOutcome.Unprojectable)?.Reason);
        Assert.IsNotType<Formula.Placeholder>(((ProjectionOutcome.Projected)outcome).Formula);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void LetSubstitutionPreservesOuterVariablesUnderBinders(bool nondependent)
    {
        var expression = new LeanExpr.Pi("bd", Real,
            new LeanExpr.Let(nondependent, Real, new LeanExpr.Bound(0),
                new LeanExpr.Pi("bd", Real, Equality(new LeanExpr.Bound(1), new LeanExpr.Bound(0)))));
        Assert.Equal(@"\forall x0 \in \mathrm{Real},\; \forall x1 \in \mathrm{Real},\; \mathit{x0} = \mathit{x1}", Render(expression));
    }

    [Fact]
    public void NestedLetsRespectShadowingAndRemoveTheirBinderSlots()
    {
        var expression = new LeanExpr.Let(false, Real, Number(7),
            new LeanExpr.Let(false, Real, new LeanExpr.Bound(0),
                Equality(new LeanExpr.Bound(0), new LeanExpr.Bound(1))));
        Assert.Equal("7 = 7", Render(expression));
    }

    [Fact]
    public void LetCannotHideAnUnsupportedUsedValueOrAnUnboundVariable()
    {
        Assert.IsType<ProjectionOutcome.Unprojectable>(StatementProjector.Project(
            new LeanExpr.Let(false, Real, Constant("Unknown.value"), new LeanExpr.Bound(0))));
        Assert.IsType<ProjectionOutcome.Unprojectable>(StatementProjector.Project(
            new LeanExpr.Let(false, Real, Number(7), new LeanExpr.Bound(1))));
    }

    [Theory]
    [InlineData("LE.le", 4, "2 \\le 5")]
    [InlineData("LT.lt", 4, "2 < 5")]
    [InlineData("HAdd.hAdd", 6, "2 + 5")]
    [InlineData("HSub.hSub", 6, "2 - 5")]
    public void ArithmeticPreservesOrderedSemanticOperands(string name, int arity, string expected)
    {
        var arguments = Enumerable.Repeat<LeanExpr>(Constant("Elaboration.instance"), arity - 2)
            .Concat([Number(2), Number(5)]).ToArray();
        Assert.Equal(expected, Render(Apply(Constant(name), arguments)));
        Assert.IsType<ProjectionOutcome.Unprojectable>(StatementProjector.Project(
            Apply(Constant(name), arguments[..^1])));
        arguments[^1] = Constant("Unknown.operand");
        Assert.IsType<ProjectionOutcome.Unprojectable>(StatementProjector.Project(Apply(Constant(name), arguments)));
    }

    [Fact]
    public void LogDerivativeRetainsFunctionAndEvaluationPoint()
    {
        var arguments = Enumerable.Repeat<LeanExpr>(Constant("Elaboration.instance"), 5)
            .Concat([Constant("Real.exp"), Number(2)]).ToArray();
        Assert.Equal(@"\mathrm{logDeriv}\left(\mathrm{exp}, 2\right)", Render(Apply(Constant("logDeriv"), arguments)));
        Assert.IsType<ProjectionOutcome.Unprojectable>(StatementProjector.Project(
            Apply(Constant("logDeriv"), arguments[..^1])));
        arguments[^2] = Constant("Unknown.function");
        Assert.IsType<ProjectionOutcome.Unprojectable>(StatementProjector.Project(Apply(Constant("logDeriv"), arguments)));
    }

    [Theory]
    [InlineData("LE.le", "2 \\le 5 \\Rightarrow 7 = 7")]
    [InlineData("LT.lt", "2 < 5 \\Rightarrow 7 = 7")]
    public void OrderedHypothesesRemainImplicationPremises(string name, string expected)
    {
        var premise = Apply(Constant(name), Real, Constant("Elaboration.instance"), Number(2), Number(5));
        Assert.Equal(expected, Render(new LeanExpr.Pi("bd", premise, Equality(Number(7), Number(7)))));
    }

    public static IEnumerable<object[]> SemanticFamilies()
    {
        yield return ["Continuous", 4, 5, 5, "Continuous"];
        yield return ["ContinuousAt", 4, 6, 6, "ContinuousAt"];
        yield return ["ContinuousOn", 4, 6, 6, "ContinuousOn"];
        yield return ["Summable", 4, 6, 6, "Summable"];
        yield return ["HasSum", 4, 7, 7, "HasSum"];
        yield return ["tsum", 4, 6, 6, "tsum"];
        yield return ["Finset.sum", 3, 5, 5, "sum"];
        yield return ["logDeriv", 5, 7, 7, "logDeriv"];
        yield return ["SummationFilter.unconditional", 0, 1, 1, "unconditional"];
        yield return ["MeasureTheory.Integrable", 5, 7, 7, "Integrable"];
        yield return ["MeasureTheory.IntegrableOn", 5, 8, 8, "IntegrableOn"];
        yield return ["MeasureTheory.AEStronglyMeasurable", 5, 7, 7, "AEStronglyMeasurable"];
        yield return ["MeasureTheory.integral", 5, 7, 7, "integral"];
        yield return ["MeasureTheory.Measure.restrict", 2, 4, 4, "restrict"];
        yield return ["MeasureTheory.MeasureSpace.volume", 0, 2, 2, "volume"];
        yield return ["FourierTransform.fourier", 3, 4, 5, "fourier"];
        yield return ["Set.Ioi", 2, 3, 3, "Ioi"];
        yield return ["Set.Ici", 2, 3, 3, "Ici"];
        yield return ["Finset.Ioc", 3, 5, 5, "Ioc"];
        yield return ["Max.max", 2, 4, 4, "max"];
        yield return ["Complex.im", 0, 1, 1, "im"];
        yield return ["Complex.digamma", 0, 1, 1, "digamma"];
        yield return ["deriv", 6, 8, 8, "deriv"];
        yield return ["riemannZeta", 0, 1, 1, "riemannZeta"];
        yield return ["LSeries.term", 0, 3, 3, "LSeriesTerm"];
        yield return ["ArithmeticFunction.vonMangoldt", 0, 1, 1, "vonMangoldt"];
        yield return ["Equiv.Perm", 0, 1, 1, "Perm"];
        yield return ["Subtype", 0, 2, 2, "Subtype"];
        yield return ["Set", 0, 1, 1, "Set"];
        yield return ["D5.S3.Weil.ZeroSum.ZeroData.multiplicity", 0, 2, 2, "ZeroDataMultiplicity"];
        yield return ["D5.S3.Weil.ZeroSum.ZeroData.zero", 0, 2, 2, "ZeroDataZero"];
        yield return ["D5.S3.Arith.Robin.CompleteMertensPeak.U", 0, 1, 1, "U"];
        yield return ["D5.S3.Weil.Mertens.IntegratedExplicit.actualCoeff", 0, 1, 1, "actualCoeff"];
        yield return ["D5.S3.Weil.Mertens.IntegratedExplicit.actualH", 0, 1, 1, "actualH"];
        yield return ["D5.S3.Weil.Mertens.IntegratedExplicit.mangoldtRamp", 0, 1, 2, "mangoldtRamp"];
        yield return ["D5.S3.Weil.Mertens.IntegratedExplicit.mangoldtPart", 0, 1, 1, "mangoldtPart"];
        yield return ["D5.S3.Weil.Mertens.IntegratedExplicit.transformLine", 0, 1, 1, "transformLine"];
        yield return ["D5.S3.Weil.Mertens.IntegratedExplicit.trivialCoeff", 0, 1, 1, "trivialCoeff"];
        yield return ["D5.S3.Weil.Mertens.IntegratedExplicit.trivialT", 0, 1, 1, "trivialT"];
        yield return ["D5.S3.Weil.Mertens.IntegratedExplicit.explicitDiscrepancy", 0, 1, 1, "explicitDiscrepancy"];
        yield return ["D5.S3.Weil.Mertens.IntegratedExplicit.explicitFourierResidual", 0, 1, 1, "explicitFourierResidual"];
        yield return ["D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds.actualZero", 0, 1, 1, "actualZero"];
    }

    [Theory]
    [MemberData(nameof(SemanticFamilies))]
    public void SemanticFamiliesRetainEveryOperandAndRejectUnknownOrUnboundOperands(
        string name, int prefix, int minimum, int maximum, string notation)
    {
        for (var arity = minimum; arity <= maximum; arity++)
        {
            var arguments = Enumerable.Repeat(Real, prefix)
                .Concat(Enumerable.Range(0, arity - prefix).Select(index => Number((uint)(index + 2)))).ToArray();
            var formula = Assert.IsType<Formula.Apply>(Assert.IsType<ProjectionOutcome.Projected>(
                StatementProjector.Project(Apply(Constant(name), arguments))).Formula);
            Assert.Equal(notation, Assert.IsType<Formula.NamedConstant>(formula.Function).Name.Value);
            Assert.Equal(Enumerable.Range(0, arity - prefix).Select(index => new Formula.Number(index + 2)),
                formula.Arguments.Cast<Formula.Number>());
            for (var index = prefix; index < arity; index++)
            {
                var changed = arguments.ToArray();
                changed[index] = Constant("Unknown.semanticOperand");
                Assert.IsType<ProjectionOutcome.Unprojectable>(StatementProjector.Project(Apply(Constant(name), changed)));
                changed[index] = new LeanExpr.Bound(0);
                Assert.IsType<ProjectionOutcome.Unprojectable>(StatementProjector.Project(Apply(Constant(name), changed)));
                var bound = Assert.IsType<Formula.Bind>(Assert.IsType<ProjectionOutcome.Projected>(
                    StatementProjector.Project(new LeanExpr.Pi("bd", Real, Apply(Constant(name), changed)))).Formula);
                var application = Assert.IsType<Formula.Apply>(bound.Body);
                Assert.Equal("x0", Assert.IsType<Formula.Symbol>(application.Arguments[index - prefix]).Name.Value);
                changed[index] = new LeanExpr.Bound(1);
                Assert.IsType<ProjectionOutcome.Unprojectable>(StatementProjector.Project(
                    new LeanExpr.Pi("bd", Real, Apply(Constant(name), changed))));
            }
        }
        Assert.False(ProjectionDenoiser.TryClean(name, Enumerable.Repeat(Real, minimum - 1).ToImmutableArray(), out _));
        Assert.False(ProjectionDenoiser.TryClean(name, Enumerable.Repeat(Real, maximum + 1).ToImmutableArray(), out _));
        var alias = "Unknown." + name.Split('.').Last();
        Assert.IsType<ProjectionOutcome.Unprojectable>(StatementProjector.Project(Constant(alias)));
        Assert.IsType<ProjectionOutcome.Unprojectable>(StatementProjector.Project(
            Apply(Constant(alias), Enumerable.Repeat(Real, maximum).ToArray())));
    }

    [Fact]
    public void PowersRetainBothOperandsAndRejectMalformedOrUnboundTerms()
    {
        var arguments = new LeanExpr[] { Real, Constant("Nat"), Real, Constant("Elaboration.instance"), Number(2), Number(5) };
        var power = Assert.IsType<Formula.Power>(Assert.IsType<ProjectionOutcome.Projected>(
            StatementProjector.Project(Apply(Constant("HPow.hPow"), arguments))).Formula);
        Assert.Equal(new Formula.Number(2), power.Base);
        Assert.Equal(new Formula.Number(5), power.Exponent);
        Assert.IsType<ProjectionOutcome.Unprojectable>(StatementProjector.Project(Apply(Constant("HPow.hPow"), arguments[..^1])));
        for (var index = 4; index < 6; index++)
        {
            var changed = arguments.ToArray();
            changed[index] = Constant("Unknown.powerOperand");
            Assert.IsType<ProjectionOutcome.Unprojectable>(StatementProjector.Project(Apply(Constant("HPow.hPow"), changed)));
            changed[index] = new LeanExpr.Bound(0);
            Assert.IsType<ProjectionOutcome.Unprojectable>(StatementProjector.Project(Apply(Constant("HPow.hPow"), changed)));
        }
    }

    [Theory]
    [InlineData("bi")]
    [InlineData("bs")]
    public void ImplicitScalarValuesRemainQuantified(string info) =>
        Assert.Equal(@"\forall x0 \in \mathrm{Real},\; \mathit{x0} = 7",
            Render(new LeanExpr.Pi(info, Real, Equality(new LeanExpr.Bound(0), Number(7)))));

    [Fact]
    public void FunctionParametersHaveArrowDomains()
    {
        var domain = new LeanExpr.Pi("bd", Real, Real);
        var formula = Assert.IsType<Formula.Bind>(Assert.IsType<ProjectionOutcome.Projected>(
            StatementProjector.Project(new LeanExpr.Pi("bi", domain,
                Equality(new LeanExpr.Bound(0), new LeanExpr.Bound(0))))).Formula);
        Assert.IsType<Formula.TypeArrow>(formula.Domain);
        Assert.Equal(new Formula.Symbol(FormulaIdentifier.Create("x0")), Assert.IsType<Formula.Relation>(formula.Body).Left);
    }

    [Fact]
    public void AnalyticFunctionLambdasRetainTypesAndCaptureOuterValues()
    {
        var lambda = new LeanExpr.Lambda("bd", Real, new LeanExpr.Bound(1));
        var arguments = new LeanExpr[] { Real, Real, Real, Real, lambda };
        var rendered = Render(new LeanExpr.Pi("bd", Real, Apply(Constant("Continuous"), arguments)));
        Assert.Contains(@"\lambda \mathit{x1}:\mathrm{Real}. \mathit{x0}", rendered, StringComparison.Ordinal);
        Assert.Equal(1, rendered.Split(@"\forall", StringSplitOptions.None).Length - 1);
        arguments[^1] = new LeanExpr.Lambda("bd", Constant("Unknown.domain"), new LeanExpr.Bound(0));
        Assert.IsType<ProjectionOutcome.Unprojectable>(StatementProjector.Project(Apply(Constant("Continuous"), arguments)));
        arguments[^1] = new LeanExpr.Lambda("bd", Real, new LeanExpr.Bound(1));
        Assert.IsType<ProjectionOutcome.Unprojectable>(StatementProjector.Project(Apply(Constant("Continuous"), arguments)));
    }

    [Fact]
    public void MeasuresKeepTheirSpaceAndInstanceAndCannotHideUnsupportedChoices()
    {
        var measure = Apply(Constant("MeasureTheory.MeasureSpace.volume"), Real, Constant("Real.measureSpace"));
        Assert.Equal(@"\mathrm{volume}\left(\mathrm{Real}, \mathrm{RealMeasureSpace}\right)", Render(measure));
        Assert.IsType<ProjectionOutcome.Unprojectable>(StatementProjector.Project(
            Apply(Constant("MeasureTheory.MeasureSpace.volume"), Real, Constant("Unknown.measureSpace"))));
    }

    [Fact]
    public void ZeroDataProjectionsRetainTheDataObjectAndIndex()
    {
        var data = Constant("D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds.actualData");
        var projected = Render(Apply(Constant("D5.S3.Weil.ZeroSum.ZeroData.multiplicity"), data, Number(5)));
        Assert.Equal(@"\mathrm{ZeroDataMultiplicity}\left(\mathrm{actualData}, 5\right)", projected);
        Assert.IsType<ProjectionOutcome.Unprojectable>(StatementProjector.Project(
            Apply(Constant("D5.S3.Weil.ZeroSum.ZeroData.multiplicity"), Constant("Unknown.data"), Number(5))));
        Assert.IsType<ProjectionOutcome.Unprojectable>(StatementProjector.Project(
            Constant("Unknown.actualData")));
    }

    [Theory]
    [InlineData("LE.le", 4)]
    [InlineData("LT.lt", 4)]
    [InlineData("HAdd.hAdd", 6)]
    [InlineData("HSub.hSub", 6)]
    public void OrderedOperationsKeepBothBoundOperandsAndRejectUnboundOnes(string name, int arity)
    {
        for (var position = arity - 2; position < arity; position++)
        {
            var arguments = Enumerable.Repeat(Real, arity - 2).Concat([Number(2), Number(5)]).ToArray();
            arguments[position] = new LeanExpr.Bound(0);
            Assert.IsType<ProjectionOutcome.Unprojectable>(StatementProjector.Project(Apply(Constant(name), arguments)));
            var rendered = Render(new LeanExpr.Pi("bd", Real, Apply(Constant(name), arguments)));
            Assert.Contains(@"\mathit{x0}", rendered, StringComparison.Ordinal);
            Assert.DoesNotContain(@"\mathord{\cdot}", rendered, StringComparison.Ordinal);
            arguments[position] = new LeanExpr.Bound(1);
            Assert.IsType<ProjectionOutcome.Unprojectable>(StatementProjector.Project(
                new LeanExpr.Pi("bd", Real, Apply(Constant(name), arguments))));
        }
    }

    [Theory]
    [InlineData("Finset.sum", 3, 1)]
    [InlineData("logDeriv", 5, 0)]
    public void FunctionSlotsRetainTypedLambdasAcrossLetSubstitution(string name, int prefix, int position)
    {
        var arguments = Enumerable.Repeat(Real, prefix).Concat([Number(2), Number(5)]).ToArray();
        arguments[prefix + position] = new LeanExpr.Lambda("bd", Real,
            new LeanExpr.Let(false, Real, new LeanExpr.Bound(1), new LeanExpr.Bound(0)));
        var rendered = Render(new LeanExpr.Pi("bd", Real, Apply(Constant(name), arguments)));
        Assert.Contains(@"\lambda \mathit{x1}:\mathrm{Real}. \mathit{x0}", rendered, StringComparison.Ordinal);
        Assert.Equal(1, rendered.Split(@"\forall", StringSplitOptions.None).Length - 1);
    }

    [Theory]
    [InlineData("starRingEnd", "starRingEnd", new int[] { 0 })]
    [InlineData("D5.S3.Fourier.FinitePoisson.annihilator", "annihilator", new int[] { 0, 2 })]
    public void NonconsecutiveSemanticArgumentsSurviveClassErasure(string name, string notation, int[] indices)
    {
        var arguments = new LeanExpr[] { Number(2), Constant("Elaboration.instance"), Number(5) };
        var application = Assert.IsType<Formula.Apply>(Assert.IsType<ProjectionOutcome.Projected>(
            StatementProjector.Project(Apply(Constant(name), arguments))).Formula);
        Assert.Equal(notation, Assert.IsType<Formula.NamedConstant>(application.Function).Name.Value);
        Assert.Equal(indices.Select(index => new Formula.Number(index == 0 ? 2 : 5)), application.Arguments.Cast<Formula.Number>());
        foreach (var index in indices)
        {
            var changed = arguments.ToArray();
            changed[index] = Constant("Unknown.semanticOperand");
            Assert.IsType<ProjectionOutcome.Unprojectable>(StatementProjector.Project(Apply(Constant(name), changed)));
            changed[index] = new LeanExpr.Bound(0);
            Assert.IsType<ProjectionOutcome.Unprojectable>(StatementProjector.Project(Apply(Constant(name), changed)));
            var bound = Assert.IsType<Formula.Bind>(Assert.IsType<ProjectionOutcome.Projected>(
                StatementProjector.Project(new LeanExpr.Pi("bd", Real, Apply(Constant(name), changed)))).Formula);
            Assert.IsType<Formula.Symbol>(Assert.IsType<Formula.Apply>(bound.Body).Arguments[Array.IndexOf(indices, index)]);
        }
        Assert.IsType<ProjectionOutcome.Unprojectable>(StatementProjector.Project(Apply(Constant(name), arguments[..^1])));
        Assert.IsType<ProjectionOutcome.Unprojectable>(StatementProjector.Project(Apply(Constant(name), [.. arguments, Number(7)])));
        Assert.IsType<ProjectionOutcome.Unprojectable>(StatementProjector.Project(Constant("Unknown." + name.Split('.').Last())));
    }

    [Fact]
    public void MembershipRetainsTheElementAndCollectionInLeanOrder()
    {
        var arguments = new LeanExpr[] { Real, Real, Constant("Elaboration.instance"), Number(2), Number(5) };
        Assert.Equal(@"5 \in 2", Render(Apply(Constant("Membership.mem"), arguments)));
        for (var index = 3; index < 5; index++)
        {
            var changed = arguments.ToArray();
            changed[index] = Constant("Unknown.membershipOperand");
            Assert.IsType<ProjectionOutcome.Unprojectable>(StatementProjector.Project(Apply(Constant("Membership.mem"), changed)));
            changed[index] = new LeanExpr.Bound(0);
            Assert.IsType<ProjectionOutcome.Unprojectable>(StatementProjector.Project(Apply(Constant("Membership.mem"), changed)));
            var bind = Assert.IsType<Formula.Bind>(Assert.IsType<ProjectionOutcome.Projected>(
                StatementProjector.Project(new LeanExpr.Pi("bd", Real, Apply(Constant("Membership.mem"), changed)))).Formula);
            var relation = Assert.IsType<Formula.Relation>(bind.Body);
            Assert.IsType<Formula.Symbol>(index == 3 ? relation.Right : relation.Left);
        }
        Assert.IsType<ProjectionOutcome.Unprojectable>(StatementProjector.Project(Apply(Constant("Membership.mem"), arguments[..^1])));
    }

    [Fact]
    public void ActualCompleteHPackagePreservesAllFiveTypedCoefficientApplications()
    {
        var pin = ExpansionPins().Single(row => (string)row[0] ==
            "D5.S3.Weil.Mertens.IntegratedExplicit.actual_complete_H_package");
        var formula = Assert.IsType<ProjectionOutcome.Projected>(StatementProjector.Project(
            StatementV1Decoder.Decode((string)pin[1]).Type)).Formula;
        var nodes = Descendants(formula).ToArray();
        Assert.DoesNotContain(nodes, node => node is Formula.Placeholder);
        Assert.DoesNotContain(nodes.OfType<Formula.Apply>(), application => application.Function is Formula.Bind);
        var applications = nodes.OfType<Formula.Apply>()
            .Where(application => application.Function is Formula.LatexSequence).ToArray();
        Assert.Equal(5, applications.Length);
        Assert.Equal(new[] { "x2", "x2", "x2", "x4", "x5" }, applications.Select(application =>
            Assert.IsType<Formula.Symbol>(Assert.Single(application.Arguments)).Name.Value));
        foreach (var application in applications)
        {
            var lambda = Assert.IsType<Formula.LatexSequence>(application.Function);
            Assert.Equal(new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), lambda.Items[0]);
            Assert.Equal(new Formula.LatexMacro(FormulaLatexMacro.LambdaLower), lambda.Items[1]);
            var variable = Assert.IsType<Formula.Symbol>(lambda.Items[3]);
            Assert.Equal(new Formula.NamedConstant(FormulaIdentifier.Create("Nat")), lambda.Items[5]);
            var coefficient = Assert.IsType<Formula.Fraction>(lambda.Items[8]);
            Assert.Equal(new Formula.Number(1), coefficient.Numerator);
            var denominator = Assert.IsType<Formula.Binary>(coefficient.Denominator);
            Assert.Equal(FormulaBinaryOperator.Multiply, denominator.Operator);
            var zero = Assert.IsType<Formula.Apply>(denominator.Left);
            Assert.Equal(new Formula.NamedConstant(FormulaIdentifier.Create("actualZero")), zero.Function);
            Assert.Equal(variable, Assert.Single(zero.Arguments));
            var complement = Assert.IsType<Formula.Binary>(denominator.Right);
            Assert.Equal(FormulaBinaryOperator.Subtract, complement.Operator);
            Assert.Equal(new Formula.Number(1), complement.Left);
            var otherZero = Assert.IsType<Formula.Apply>(complement.Right);
            Assert.Equal(zero.Function, otherZero.Function);
            Assert.Equal(variable, Assert.Single(otherZero.Arguments));
            Assert.Equal(new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), lambda.Items[^1]);
        }
    }

    [Fact]
    public void PilotSetLambdasPreserveTheirNamedCarrierDomain()
    {
        var pin = ExpansionPins().Single(row => (string)row[0] ==
            "D5.S1.Solenoid.hiddenFiber_closed_compact_seqCompact");
        var formula = Assert.IsType<ProjectionOutcome.Projected>(StatementProjector.Project(
            StatementV1Decoder.Decode((string)pin[1]).Type)).Formula;
        var lambdas = Descendants(formula).OfType<Formula.LatexSequence>().ToArray();
        Assert.NotEmpty(lambdas);
        Assert.All(lambdas, lambda => Assert.Equal(
            new Formula.NamedConstant(FormulaIdentifier.Create("UniversalSolenoid")), lambda.Items[5]));
    }

    [Theory]
    [InlineData(0, "Nat")]
    [InlineData(1, "Nat")]
    [InlineData(2, "Nat")]
    [InlineData(3, "Nat")]
    [InlineData(0, "Real")]
    [InlineData(1, "Real")]
    [InlineData(2, "Real")]
    [InlineData(3, "Real")]
    public void FunctionApplicationsPreserveTypedCurriedLambdasThroughAliases(int shape, string domain)
    {
        var type = Constant(domain);
        var functionType = new LeanExpr.Pi("bd", type, new LeanExpr.Pi("bd", type, type));
        var lambda = new LeanExpr.Lambda("bd", type, new LeanExpr.Lambda("bd", type,
            Apply(Constant("HSub.hSub"), type, type, type, Constant("Elaboration.instance"),
                new LeanExpr.Bound(1), new LeanExpr.Bound(0))));
        LeanExpr function = shape switch
        {
            0 => lambda,
            1 => new LeanExpr.Let(false, functionType, lambda, new LeanExpr.Bound(0)),
            2 => new LeanExpr.Metadata(lambda),
            _ => new LeanExpr.Let(true, functionType, lambda,
                new LeanExpr.Let(false, functionType, new LeanExpr.Bound(0), new LeanExpr.Bound(0)))
        };
        var rendered = Render(Apply(function, Number(2), Number(5)));
        Assert.Equal(@"(\lambda \mathit{x0}:\mathrm{" + domain + @"}. (\lambda \mathit{x1}:\mathrm{" + domain
            + @"}. \mathit{x0} - \mathit{x1}))\left(2, 5\right)", rendered);
    }

    [Fact]
    public void AliasedLambdaApplicationsCannotCaptureInterveningBinders()
    {
        var expression = new LeanExpr.Pi("bd", Real,
            new LeanExpr.Let(false, new LeanExpr.Pi("bd", Real, Real),
                new LeanExpr.Lambda("bd", Real, new LeanExpr.Bound(1)),
                new LeanExpr.Pi("bd", Real, Equality(
                    Apply(new LeanExpr.Bound(1), new LeanExpr.Bound(0)), new LeanExpr.Bound(2)))));
        Assert.Equal(@"\forall x0 \in \mathrm{Real},\; \forall x1 \in \mathrm{Real},\; "
            + @"(\lambda \mathit{x2}:\mathrm{Real}. \mathit{x0})\left(\mathit{x1}\right) = \mathit{x0}",
            Render(expression));
    }

    [Fact]
    public void AliasedLambdaDomainsKeepTheirOuterTypeParameters()
    {
        var domain = Apply(Constant("ZMod"), new LeanExpr.Bound(0));
        var functionType = new LeanExpr.Pi("bd", domain, Apply(Constant("ZMod"), new LeanExpr.Bound(1)));
        var expression = new LeanExpr.Pi("bd", Constant("Nat"),
            new LeanExpr.Let(false, functionType, new LeanExpr.Lambda("bd", domain, new LeanExpr.Bound(0)),
                new LeanExpr.Pi("bd", Apply(Constant("ZMod"), new LeanExpr.Bound(1)),
                    Apply(Constant("Eq"), Apply(Constant("ZMod"), new LeanExpr.Bound(2)),
                        Apply(new LeanExpr.Bound(1), new LeanExpr.Bound(0)), new LeanExpr.Bound(0)))));
        Assert.Equal(@"\forall x0 \in \mathrm{Nat},\; \forall x1 \in \mathrm{ZMod}\left(\mathit{x0}\right),\; "
            + @"(\lambda \mathit{x2}:\mathrm{ZMod}\left(\mathit{x0}\right). \mathit{x2})"
            + @"\left(\mathit{x1}\right) = \mathit{x1}", Render(expression));
    }

    [Fact]
    public void GeneralLambdaOperandsKeepDomainsAndRejectUnsupportedUsedTerms()
    {
        var identity = new LeanExpr.Lambda("bd", Real, new LeanExpr.Bound(0));
        var functionType = new LeanExpr.Pi("bd", Real, Real);
        Assert.Equal(@"(\lambda \mathit{x0}:\mathrm{Real}. \mathit{x0}) = "
            + @"(\lambda \mathit{x0}:\mathrm{Real}. \mathit{x0})",
            Render(Apply(Constant("Eq"), functionType, identity, identity)));
        Assert.IsType<ProjectionOutcome.Unprojectable>(StatementProjector.Project(
            new LeanExpr.Lambda("bd", Constant("Unknown.domain"), new LeanExpr.Bound(0))));
        Assert.IsType<ProjectionOutcome.Unprojectable>(StatementProjector.Project(
            Apply(new LeanExpr.Lambda("bd", Constant("Unknown.domain"), new LeanExpr.Bound(0)), Number(2))));
        Assert.IsType<ProjectionOutcome.Unprojectable>(StatementProjector.Project(
            Apply(new LeanExpr.Lambda("bd", Real, Constant("Unknown.body")), Number(2))));
        Assert.IsType<ProjectionOutcome.Unprojectable>(StatementProjector.Project(
            Apply(new LeanExpr.Lambda("bd", Real, new LeanExpr.Bound(1)), Number(2))));
        Assert.IsType<ProjectionOutcome.Unprojectable>(StatementProjector.Project(
            Apply(identity, Constant("Unknown.argument"))));
    }

    private static IEnumerable<Formula> Descendants(Formula formula)
    {
        yield return formula;
        foreach (var property in formula.GetType().GetProperties())
        {
            var value = property.GetValue(formula);
            var children = value is Formula child ? new[] { child }
                : value as IEnumerable<Formula> ?? [];
            foreach (var descendant in children.SelectMany(Descendants)) yield return descendant;
        }
    }

    private static LeanExpr Real => Constant("Real");
    private static LeanExpr Constant(string name) => new LeanExpr.Constant(name, []);
    private static LeanExpr Number(uint value) => new LeanExpr.Literal(value);
    private static LeanExpr Apply(LeanExpr function, params LeanExpr[] arguments) =>
        arguments.Aggregate(function, (current, argument) => new LeanExpr.App(current, argument));
    private static LeanExpr Equality(LeanExpr left, LeanExpr right) => Apply(Constant("Eq"), Real, left, right);
    private static string Render(LeanExpr expression) => LatexWriter.Write(
        Assert.IsType<ProjectionOutcome.Projected>(StatementProjector.Project(expression)).Formula);
}
