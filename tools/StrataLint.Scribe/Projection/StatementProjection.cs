using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using System.Runtime.CompilerServices;
using System.Security.Cryptography;
using StrataLint.Engine;

namespace StrataLint.Scribe;

internal sealed record LeanStatement(ImmutableArray<string> UniverseParameters, LeanExpr Type);

internal abstract record LeanExpr
{
    internal sealed record Bound(uint Index) : LeanExpr;
    internal sealed record Free(string Name) : LeanExpr;
    internal sealed record Meta(string Name) : LeanExpr;
    internal sealed record Sort(LeanLevel Level) : LeanExpr;
    internal sealed record Constant(string Name, ImmutableArray<LeanLevel> Levels) : LeanExpr;
    internal sealed record App(LeanExpr Function, LeanExpr Argument) : LeanExpr;
    internal sealed record Lambda(string BinderInfo, LeanExpr Domain, LeanExpr Body) : LeanExpr;
    internal sealed record Pi(string BinderInfo, LeanExpr Domain, LeanExpr Body) : LeanExpr;
    internal sealed record Let(bool Nondependent, LeanExpr Type, LeanExpr Value, LeanExpr Body) : LeanExpr;
    internal sealed record Literal(object Value) : LeanExpr;
    internal sealed record Metadata(LeanExpr Body) : LeanExpr;
    internal sealed record Projection(string Name, uint Index, LeanExpr Body) : LeanExpr;
}

internal abstract record LeanLevel
{
    internal sealed record Zero : LeanLevel;
    internal sealed record Succ(LeanLevel Value) : LeanLevel;
    internal sealed record Max(LeanLevel Left, LeanLevel Right) : LeanLevel;
    internal sealed record IMax(LeanLevel Left, LeanLevel Right) : LeanLevel;
    internal sealed record Param(string Name) : LeanLevel;
    internal sealed record Meta(string Name) : LeanLevel;
}

internal static class StatementV1Decoder
{
    internal static LeanStatement Decode(string input)
    {
        try
        {
            var parser = new Parser(input);
            parser.Take("statement-v1(uparams=[");
            var parameters = parser.List(parser.Name, ']');
            parser.Take(",type=");
            var type = parser.Expr();
            if (parser.TryTake(",value="))
            {
                if (!parser.TryTake("missing")) _ = parser.Expr();
            }
            parser.Take(")");
            parser.End();
            return new LeanStatement(parameters, type);
        }
        catch (Exception exception) when (exception is not FormatException)
        {
            throw new FormatException("Malformed statement-v1 encoding.", exception);
        }
    }

    private sealed class Parser(string text)
    {
        private int position;

        internal LeanExpr Expr()
        {
            var tag = Word(2);
            return tag switch
            {
                "eb" => One(value => new LeanExpr.Bound(value.UInt())),
                "ef" => One(value => new LeanExpr.Free(value.Name())),
                "em" => One(value => new LeanExpr.Meta(value.Name())),
                "es" => One(value => new LeanExpr.Sort(value.Level())),
                "ec" => Constant(),
                "ea" => Two((left, right) => new LeanExpr.App(Expr(left), Expr(right))),
                "el" => Binder((info, domain, body) => new LeanExpr.Lambda(info, domain, body)),
                "ep" => Binder((info, domain, body) => new LeanExpr.Pi(info, domain, body)),
                "ee" => Let(),
                "ei" => Literal(),
                "ed" => One(value => new LeanExpr.Metadata(value.Expr())),
                "ej" => Projection(),
                _ => throw Error($"Unknown expression tag {tag}.")
            };
        }

        internal string Name()
        {
            var name = CanonicalLeanNameDecoder.DecodePrefix(text, position, out var consumed);
            position += consumed;
            return name;
        }

        internal LeanLevel Level()
        {
            if (TryTake("l0")) return new LeanLevel.Zero();
            var tag = Word(2);
            return tag switch
            {
                "ls" => One(value => new LeanLevel.Succ(value.Level())),
                "lm" => Two((a, b) => new LeanLevel.Max(Level(a), Level(b))),
                "li" => Two((a, b) => new LeanLevel.IMax(Level(a), Level(b))),
                "lp" => One(value => new LeanLevel.Param(value.Name())),
                "lv" => One(value => new LeanLevel.Meta(value.Name())),
                _ => throw Error($"Unknown level tag {tag}.")
            };
        }

        internal ImmutableArray<T> List<T>(Func<T> read, char close)
        {
            var values = ImmutableArray.CreateBuilder<T>();
            if (TryTake(close.ToString())) return values.ToImmutable();
            while (true)
            {
                values.Add(read());
                if (TryTake(close.ToString())) return values.ToImmutable();
                Take(",");
            }
        }

        internal void End() { if (position != text.Length) throw Error("Trailing input."); }
        internal void Take(string value) { if (!TryTake(value)) throw Error($"Expected {value}."); }
        internal bool TryTake(string value)
        {
            if (!text.AsSpan(position).StartsWith(value, StringComparison.Ordinal)) return false;
            position += value.Length;
            return true;
        }

        private LeanExpr Constant()
        {
            Take("("); var name = Name(); Take(",["); var levels = List(Level, ']'); Take(")");
            return new LeanExpr.Constant(name, levels);
        }

        private LeanExpr Binder(Func<string, LeanExpr, LeanExpr, LeanExpr> create)
        {
            Take("("); var info = Word(2); Take(","); var domain = Expr(); Take(","); var body = Expr(); Take(")");
            return create(info, domain, body);
        }

        private LeanExpr Let()
        {
            Take("("); var flag = UInt(); Take(","); var type = Expr(); Take(","); var value = Expr(); Take(","); var body = Expr(); Take(")");
            return new LeanExpr.Let(flag == 1, type, value, body);
        }

        private LeanExpr Literal()
        {
            Take("("); var tag = Word(2); Take("("); object value = tag switch { "ln" => UInt(), "lt" => Atom(), _ => throw Error("Unknown literal tag.") }; Take(")"); Take(")");
            return new LeanExpr.Literal(value);
        }

        private LeanExpr Projection()
        {
            Take("("); var name = Name(); Take(","); var index = UInt(); Take(","); var body = Expr(); Take(")");
            return new LeanExpr.Projection(name, index, body);
        }

        private T One<T>(Func<Parser, T> create) { Take("("); var result = create(this); Take(")"); return result; }
        private T Two<T>(Func<Parser, Parser, T> create) { Take("("); var left = this; var first = Capture(); Take(","); var second = Capture(); Take(")"); return create(new Parser(first), new Parser(second)); }
        private string Capture()
        {
            var start = position; var depth = 0;
            while (position < text.Length)
            {
                var c = text[position];
                if (depth == 0 && (c == ',' || c == ')')) break;
                if (c == '(' || c == '[') depth++;
                if (c == ')' || c == ']') depth--;
                position++;
            }
            return text[start..position];
        }
        private uint UInt() { var start = position; while (position < text.Length && char.IsDigit(text[position])) position++; if (start == position) throw Error("Expected unsigned integer."); return uint.Parse(text[start..position], System.Globalization.CultureInfo.InvariantCulture); }
        private string Atom() { var length = checked((int)UInt()); Take(":"); if (position + length > text.Length) throw Error("Atom exceeds input."); var result = text.Substring(position, length); position += length; return result; }
        private string Word(int length) { if (position + length > text.Length) throw Error("Unexpected end."); var result = text.Substring(position, length); position += length; return result; }
        private FormatException Error(string message) => new($"{message} At byte {Encoding.UTF8.GetByteCount(text.AsSpan(0, position))}.");
        private static LeanExpr Expr(Parser parser) { var result = parser.Expr(); parser.End(); return result; }
        private static LeanLevel Level(Parser parser) { var result = parser.Level(); parser.End(); return result; }
    }
}

internal sealed record SemanticProjectionSignature(string Notation, int DropPrefix,
    int MinimumArguments, int MaximumArguments, ImmutableArray<int> FunctionArguments,
    bool Proposition, ImmutableArray<int> ArgumentIndices = default);

internal static class SemanticProjectionSignatures
{
    // Measures, summation filters, sets, functions and evaluation points remain
    // ordered semantic operands after removing the registered elaboration prefix.
    internal static readonly ImmutableDictionary<string, SemanticProjectionSignature> Entries =
        new Dictionary<string, SemanticProjectionSignature>(StringComparer.Ordinal)
        {
            ["Continuous"] = new("Continuous", 4, 5, 5, [0], true),
            ["ContinuousAt"] = new("ContinuousAt", 4, 6, 6, [0], true),
            ["ContinuousOn"] = new("ContinuousOn", 4, 6, 6, [0], true),
            ["Summable"] = new("Summable", 4, 6, 6, [0], true),
            ["HasSum"] = new("HasSum", 4, 7, 7, [0], true),
            ["tsum"] = new("tsum", 4, 6, 6, [0], false),
            ["Finset.sum"] = new("sum", 3, 5, 5, [1], false),
            ["logDeriv"] = new("logDeriv", 5, 7, 7, [0], false),
            ["SummationFilter.unconditional"] = new("unconditional", 0, 1, 1, [], false),
            ["MeasureTheory.Integrable"] = new("Integrable", 5, 7, 7, [0], true),
            ["MeasureTheory.IntegrableOn"] = new("IntegrableOn", 5, 8, 8, [0], true),
            ["MeasureTheory.AEStronglyMeasurable"] = new("AEStronglyMeasurable", 5, 7, 7, [0], true),
            ["MeasureTheory.integral"] = new("integral", 5, 7, 7, [1], false),
            ["MeasureTheory.Measure.restrict"] = new("restrict", 2, 4, 4, [], false),
            ["MeasureTheory.MeasureSpace.volume"] = new("volume", 0, 2, 2, [], false),
            ["FourierTransform.fourier"] = new("fourier", 3, 4, 5, [0], false),
            ["Set.Ioi"] = new("Ioi", 2, 3, 3, [], false),
            ["Set.Ici"] = new("Ici", 2, 3, 3, [], false),
            ["Finset.Ioc"] = new("Ioc", 3, 5, 5, [], false),
            ["HPow.hPow"] = new("power", 4, 6, 6, [], false),
            ["Max.max"] = new("max", 2, 4, 4, [], false),
            ["Complex.im"] = new("im", 0, 1, 1, [], false),
            ["Complex.digamma"] = new("digamma", 0, 1, 1, [], false),
            ["deriv"] = new("deriv", 6, 8, 8, [0], false),
            ["riemannZeta"] = new("riemannZeta", 0, 1, 1, [], false),
            ["LSeries.term"] = new("LSeriesTerm", 0, 3, 3, [0], false),
            ["ArithmeticFunction.vonMangoldt"] = new("vonMangoldt", 0, 1, 1, [], false),
            ["Real.measureSpace"] = new("RealMeasureSpace", 0, 0, 0, [], false),
            ["Equiv.Perm"] = new("Perm", 0, 1, 1, [], false),
            ["Subtype"] = new("Subtype", 0, 2, 2, [1], false),
            ["Set"] = new("Set", 0, 1, 1, [], false),
            ["Membership.mem"] = new("membership", 3, 5, 5, [], true),
            ["starRingEnd"] = new("starRingEnd", 0, 3, 3, [], false, [0]),
            ["D5.S3.Fourier.FinitePoisson.annihilator"] = new("annihilator", 0, 3, 3, [], false, [0, 2]),
            ["D5.S3.Weil.ZeroSum.ZeroData.multiplicity"] = new("ZeroDataMultiplicity", 0, 2, 2, [], false),
            ["D5.S3.Weil.ZeroSum.ZeroData.zero"] = new("ZeroDataZero", 0, 2, 2, [], false),
            ["D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds.actualData"] = new("actualData", 0, 0, 0, [], false),
            ["D5.S3.Arith.Robin.CompleteMertensPeak.U"] = new("U", 0, 1, 1, [], false),
            ["D5.S3.Weil.Mertens.IntegratedExplicit.actualCoeff"] = new("actualCoeff", 0, 1, 1, [], false),
            ["D5.S3.Weil.Mertens.IntegratedExplicit.actualH"] = new("actualH", 0, 1, 1, [], false),
            ["D5.S3.Weil.Mertens.IntegratedExplicit.mangoldtRamp"] = new("mangoldtRamp", 0, 1, 2, [], false),
            ["D5.S3.Weil.Mertens.IntegratedExplicit.mangoldtPart"] = new("mangoldtPart", 0, 1, 1, [], false),
            ["D5.S3.Weil.Mertens.IntegratedExplicit.transformLine"] = new("transformLine", 0, 1, 1, [], false),
            ["D5.S3.Weil.Mertens.IntegratedExplicit.trivialCoeff"] = new("trivialCoeff", 0, 1, 1, [], false),
            ["D5.S3.Weil.Mertens.IntegratedExplicit.trivialT"] = new("trivialT", 0, 1, 1, [], false),
            ["D5.S3.Weil.Mertens.IntegratedExplicit.explicitDiscrepancy"] = new("explicitDiscrepancy", 0, 1, 1, [], false),
            ["D5.S3.Weil.Mertens.IntegratedExplicit.explicitFourierResidual"] = new("explicitFourierResidual", 0, 1, 1, [], false),
            ["D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds.actualZero"] = new("actualZero", 0, 1, 1, [], false),
        }.ToImmutableDictionary(StringComparer.Ordinal);
}

internal static class ProjectionNotation
{
    internal static readonly ImmutableDictionary<string, string> Entries = new Dictionary<string, string>(StringComparer.Ordinal)
    {
        ["Eq"] = "=", ["Ne"] = "!=", ["Not"] = "not", ["And"] = "and", ["Or"] = "or", ["Iff"] = "iff",
        ["Complex"] = "Complex", ["Real"] = "Real", ["Int"] = "Int", ["Nat"] = "Nat",
        ["Membership.mem"] = "in", ["norm"] = "norm", ["Exists"] = "exists",
        ["D5.S3.Weil.LabeledZeta.LedgerLength"] = "LedgerLength",
        ["D5.S3.Weil.LabeledZeta.criticalAbscissa"] = "criticalAbscissa",
        ["D5.S3.Weil.Convention.criticalAbscissa"] = "criticalAbscissa",
        ["D5.S3.Zeros.ScalingRegisterRigidity.applyRegister"] = "applyRegister",
        ["D5.S3.Weil.HalfDensity.halfDensityReading"] = "halfDensityReading",
        ["D5.S3.Weil.CriticalLine.halfDensityReading"] = "halfDensityReading",
        ["D5.S3.Weil.ReflectionLedger.scalingLedger"] = "scalingLedger",
        ["D5.S0.Conventions.TotalCode.TotalCode"] = "TotalCode",
        ["D5.S0.Conventions.TotalCode.TotalCode.data"] = "TotalCode.data",
        ["D5.S0.Conventions.TotalCode.TotalCode.rules"] = "TotalCode.rules",
        ["D5.S0.Conventions.TotalCode.TotalCode.ledger"] = "TotalCode.ledger",
        ["D5.S3.Zeros.ScalingRegisterRigidity.ScalingRegister"] = "ScalingRegister",
        ["D5.S3.Zeros.ScalingRegisterRigidity.AddressIndependent"] = "AddressIndependent",
        ["D5.S3.Zeros.ScalingRegisterRigidity.RealizesAt"] = "RealizesAt",
        ["AnalyticOnNhd"] = "AnalyticOnNhd", ["IsPreconnected"] = "IsPreconnected",
        ["Filter.EventuallyEq"] = "EventuallyEq", ["nhds"] = "nhds",
        ["Real.exp"] = "exp", ["Complex.exp"] = "exp", ["Complex.I"] = "I", ["Real.pi"] = "pi",
        ["Int.castAddHom"] = "castAddHom", ["Int.cast"] = "cast", ["Nat.cast"] = "cast",
        ["Complex.ofReal"] = "ofReal",
        ["DFunLike.coe"] = "coe", ["HMul.hMul"] = "multiply", ["HDiv.hDiv"] = "divide",
        ["Complex.re"] = "re",
        ["IsClosed"] = "IsClosed", ["IsCompact"] = "IsCompact", ["IsSeqCompact"] = "IsSeqCompact",
        ["setOf"] = "setOf", ["Set.ofPred"] = "setOf", ["AddSubgroup"] = "AddSubgroup",
        ["ZMod"] = "ZMod",
        ["D5.S1.Dynamics.UniversalSolenoid"] = "UniversalSolenoid",
        ["D5.S1.Dynamics.UniversalSolenoid.projection"] = "projection",
        ["Finset.sum"] = "sum", ["Finset.univ"] = "univ", ["Set.univ"] = "univ",
        ["Subtype.val"] = "val",
        ["Fintype.card"] = "card",
        ["Real.log"] = "log", ["Real.eulerMascheroniConstant"] = "eulerMascheroniConstant",
        ["D5.S3.Zeros.CompletedZeta.xiReading"] = "xiReading",
        ["D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds.firstLiMass"] = "firstLiMass",
    }.ToImmutableDictionary(StringComparer.Ordinal);
}

internal sealed record DenoiseRule(int DropPrefix, int? KeepLast = null, ImmutableArray<int> Keep = default, int? ArgumentCount = null);

internal static class ProjectionDenoiser
{
    internal static readonly ImmutableDictionary<string, DenoiseRule> Rules = new Dictionary<string, DenoiseRule>(StringComparer.Ordinal)
    {
        ["Eq"] = new(0, 2), ["Ne"] = new(0, 2), ["And"] = new(0, 2), ["Or"] = new(0, 2),
        ["Iff"] = new(0, 2), ["Not"] = new(0, 1), ["Exists"] = new(0, 2),
        ["Membership.mem"] = new(0, 2), ["norm"] = new(0, 1),
        ["OfNat.ofNat"] = new(0, null, [1]), ["Neg.neg"] = new(0, 1),
        ["DFunLike.coe"] = new(0, 2), ["HMul.hMul"] = new(0, 2), ["HDiv.hDiv"] = new(0, 2),
        ["Complex.re"] = new(0, 1),
        ["LE.le"] = new(0, 2, ArgumentCount: 4),
        ["LT.lt"] = new(0, 2, ArgumentCount: 4),
        ["HAdd.hAdd"] = new(0, 2, ArgumentCount: 6),
        ["HSub.hSub"] = new(0, 2, ArgumentCount: 6),
        ["Real.log"] = new(0, ArgumentCount: 1),
        ["D5.S3.Zeros.CompletedZeta.xiReading"] = new(0, ArgumentCount: 1),
        ["IsClosed"] = new(0, 1), ["IsCompact"] = new(0, 1), ["IsSeqCompact"] = new(0, 1),
        ["setOf"] = new(0, 1), ["Set.ofPred"] = new(0, 1),
        ["AddSubgroup"] = new(0, null, [0]),
        ["ZMod"] = new(0),
        ["Finset.sum"] = new(0, 2),
        ["Finset.univ"] = new(0, 0),
        ["Set.univ"] = new(0, 0), ["Subtype.val"] = new(0, 1),
        ["Fintype.card"] = new(0, null, [0]),
        ["D5.S3.Weil.LabeledZeta.LedgerLength"] = new(0, 0),
        ["D5.S3.Weil.ReflectionLedger.scalingLedger"] = new(0, 3),
        ["D5.S3.Weil.CriticalLine.halfDensityReading"] = new(0, 3),
        ["D5.S0.Conventions.TotalCode.TotalCode"] = new(3),
        ["D5.S0.Conventions.TotalCode.TotalCode.data"] = new(3),
        ["D5.S0.Conventions.TotalCode.TotalCode.rules"] = new(3),
        ["D5.S0.Conventions.TotalCode.TotalCode.ledger"] = new(3),
        ["D5.S3.Zeros.ScalingRegisterRigidity.applyRegister"] = new(3),
        ["D5.S3.Zeros.ScalingRegisterRigidity.ScalingRegister"] = new(2),
        ["D5.S3.Zeros.ScalingRegisterRigidity.AddressIndependent"] = new(1),
        ["D5.S3.Zeros.ScalingRegisterRigidity.RealizesAt"] = new(3),
        ["AnalyticOnNhd"] = new(0, 2), ["IsPreconnected"] = new(0, 1),
        ["Filter.EventuallyEq"] = new(0, 3), ["nhds"] = new(0, 1),
        ["Real.exp"] = new(0), ["Complex.exp"] = new(0), ["Int.castAddHom"] = new(0, null, [0]),
        ["Int.cast"] = new(0, 1), ["Nat.cast"] = new(0, 1), ["Complex.ofReal"] = new(0),
    }.ToImmutableDictionary(StringComparer.Ordinal);

    internal static bool TryClean(string name, ImmutableArray<LeanExpr> arguments,
        out ImmutableArray<LeanExpr> cleaned)
    {
        if (SemanticProjectionSignatures.Entries.TryGetValue(name, out var signature))
        {
            if (arguments.Length < signature.MinimumArguments || arguments.Length > signature.MaximumArguments)
            {
                cleaned = default;
                return false;
            }
            cleaned = signature.ArgumentIndices.IsDefault
                ? arguments[signature.DropPrefix..]
                : signature.ArgumentIndices.Select(index => arguments[index]).ToImmutableArray();
            return true;
        }
        var leaf = name.Split('.').Last();
        if (!Rules.TryGetValue(name, out var rule) && !Rules.TryGetValue(leaf, out rule))
        {
            cleaned = default;
            return false;
        }
        if (rule.ArgumentCount is int argumentCount && arguments.Length != argumentCount)
        {
            cleaned = default;
            return false;
        }
        if (!rule.Keep.IsDefault)
        {
            if (rule.Keep.Any(index => index < 0 || index >= arguments.Length)) { cleaned = default; return false; }
            cleaned = rule.Keep.Select(index => arguments[index]).ToImmutableArray();
            return true;
        }
        if (rule.DropPrefix > arguments.Length) { cleaned = default; return false; }
        cleaned = arguments[rule.DropPrefix..];
        if (rule.KeepLast is int count)
        {
            if (count > cleaned.Length) { cleaned = default; return false; }
            cleaned = cleaned[^count..];
        }
        return true;
    }
}

internal abstract record ProjectionOutcome
{
    internal sealed record Projected(Formula Formula) : ProjectionOutcome;
    internal sealed record Unprojectable(string Reason) : ProjectionOutcome;
}

internal static class PropPiToImplicationRule
{
    private static readonly ImmutableHashSet<string> PropositionConstructors =
        ImmutableHashSet.Create(StringComparer.Ordinal,
            "Eq", "Ne", "Not", "And", "Or", "Iff", "Exists");

    internal static bool Matches(LeanExpr.Pi pi) =>
        pi.BinderInfo is "bd" or "bi" or "bs"
        && IsProposition(pi.Domain)
        && !ContainsBoundVariable(pi.Body, depth: 0);

    private static bool IsProposition(LeanExpr expression)
    {
        if (expression is LeanExpr.Metadata metadata)
            return IsProposition(metadata.Body);
        if (expression is LeanExpr.Pi pi)
            return IsProposition(pi.Body);
        if (expression is not LeanExpr.App)
            return false;

        var head = expression;
        while (head is LeanExpr.App app)
            head = app.Function;
        return head is LeanExpr.Constant constant
            && (PropositionConstructors.Contains(constant.Name.Split('.').Last())
                || constant.Name is "LE.le" or "LT.lt"
                || SemanticProjectionSignatures.Entries.TryGetValue(constant.Name, out var signature)
                    && signature.Proposition);
    }

    internal static bool ContainsBoundVariable(LeanExpr expression, uint depth) => expression switch
    {
        LeanExpr.Bound bound => bound.Index == depth,
        LeanExpr.App app => ContainsBoundVariable(app.Function, depth)
            || ContainsBoundVariable(app.Argument, depth),
        LeanExpr.Lambda lambda => ContainsBoundVariable(lambda.Domain, depth)
            || ContainsBoundVariable(lambda.Body, checked(depth + 1)),
        LeanExpr.Pi pi => ContainsBoundVariable(pi.Domain, depth)
            || ContainsBoundVariable(pi.Body, checked(depth + 1)),
        LeanExpr.Let let => ContainsBoundVariable(let.Type, depth)
            || ContainsBoundVariable(let.Value, depth)
            || ContainsBoundVariable(let.Body, checked(depth + 1)),
        LeanExpr.Metadata metadata => ContainsBoundVariable(metadata.Body, depth),
        LeanExpr.Projection projection => ContainsBoundVariable(projection.Body, depth),
        _ => false
    };
}

internal static class StatementProjector
{
    internal static ProjectionOutcome Project(LeanExpr expression) => Project(expression, []);

    private static ProjectionOutcome Project(LeanExpr expression, ImmutableArray<Formula> variables)
    {
        // Zeta reduction substitutes kernel terms before assigning display binders.
        if (expression is LeanExpr.Let let)
            return Project(Instantiate(let.Body, let.Value), variables);
        if (expression is LeanExpr.Pi pi)
        {
            if (pi.BinderInfo == "bc" || pi.BinderInfo is "bi" or "bs" && pi.Domain is LeanExpr.Sort)
                return Project(pi.Body, variables.Insert(0, new Formula.Placeholder()));
            if (PropPiToImplicationRule.Matches(pi))
            {
                var premise = Project(pi.Domain, variables);
                var conclusion = Project(pi.Body, variables.Insert(0, new Formula.Placeholder()));
                if (premise is ProjectionOutcome.Unprojectable premiseFailure) return premiseFailure;
                if (conclusion is ProjectionOutcome.Unprojectable conclusionFailure) return conclusionFailure;
                return new ProjectionOutcome.Projected(new Formula.Logic(
                    ((ProjectionOutcome.Projected)premise).Formula,
                    FormulaLogicOperator.Implies,
                    ((ProjectionOutcome.Projected)conclusion).Formula));
            }
            var domain = ProjectDomain(pi.Domain, variables);
            var identifier = FormulaIdentifier.Create("x" + variables.Length);
            var symbol = new Formula.Symbol(identifier);
            var body = Project(pi.Body, variables.Insert(0, symbol));
            if (domain is ProjectionOutcome.Unprojectable domainFailure) return domainFailure;
            if (body is ProjectionOutcome.Unprojectable bodyFailure) return bodyFailure;
            var d = (ProjectionOutcome.Projected)domain;
            var b = (ProjectionOutcome.Projected)body;
            return new ProjectionOutcome.Projected(new Formula.Bind(FormulaQuantifier.ForAll, identifier, d.Formula, b.Formula));
        }

        if (expression is LeanExpr.Bound bound)
            return bound.Index < variables.Length
                ? new ProjectionOutcome.Projected(variables[(int)bound.Index])
                : new ProjectionOutcome.Unprojectable("unbound-bvar:" + bound.Index);
        if (expression is LeanExpr.Sort)
            return new ProjectionOutcome.Projected(new Formula.NamedConstant(FormulaIdentifier.Create("Type")));
        if (expression is LeanExpr.Constant constant)
        {
            var leaf = constant.Name.Split('.').Last();
            if (!TryNotation(constant.Name, out var notation))
                return new ProjectionOutcome.Unprojectable("constant:" + constant.Name);
            var canonical = new string(notation.Where(char.IsLetterOrDigit).ToArray());
            return new ProjectionOutcome.Projected(new Formula.NamedConstant(FormulaIdentifier.Create(canonical)));
        }
        if (expression is LeanExpr.Literal { Value: uint number })
            return new ProjectionOutcome.Projected(new Formula.Number(number));
        if (expression is LeanExpr.Metadata metadata) return Project(metadata.Body, variables);
        if (expression is LeanExpr.Lambda)
            return ProjectFunction(expression, variables);
        if (expression is LeanExpr.Projection projection)
        {
            var body = Project(projection.Body, variables);
            return body is ProjectionOutcome.Projected projected
                ? new ProjectionOutcome.Projected(new Formula.Apply(
                    new Formula.NamedConstant(FormulaIdentifier.Create(projection.Name.Split('.').Last())), [projected.Formula]))
                : body;
        }
        if (expression is LeanExpr.App)
        {
            var (head, arguments) = Flatten(expression);
            if (head is not LeanExpr.Constant headConstant)
            {
                var function = Project(head, variables);
                var projectedArguments = arguments.Select(argument => Project(argument, variables)).ToArray();
                var failure = projectedArguments.OfType<ProjectionOutcome.Unprojectable>().FirstOrDefault();
                if (function is ProjectionOutcome.Unprojectable functionFailure) return functionFailure;
                if (failure is not null) return failure;
                return new ProjectionOutcome.Projected(new Formula.Apply(
                    ((ProjectionOutcome.Projected)function).Formula,
                    projectedArguments.Cast<ProjectionOutcome.Projected>().Select(item => item.Formula).ToImmutableArray()));
            }
            if (!ProjectionDenoiser.TryClean(headConstant.Name, arguments, out var semanticArguments))
                return new ProjectionOutcome.Unprojectable("unregistered-elaboration-shape:" + headConstant.Name);
            SemanticProjectionSignatures.Entries.TryGetValue(headConstant.Name, out var signature);
            var projected = semanticArguments.Select((argument, index) =>
                signature is not null && signature.FunctionArguments.Contains(index)
                    ? ProjectFunction(argument, variables)
                    : Project(argument, variables)).ToArray();
            var argumentFailure = projected.OfType<ProjectionOutcome.Unprojectable>().FirstOrDefault();
            if (argumentFailure is not null) return argumentFailure;
            var values = projected.Cast<ProjectionOutcome.Projected>().Select(item => item.Formula).ToArray();
            var leaf = headConstant.Name.Split('.').Last();
            if (headConstant.Name is "LE.le" or "LT.lt")
                return new ProjectionOutcome.Projected(new Formula.Relation(values[0],
                    headConstant.Name == "LE.le" ? FormulaRelationOperator.LessThanOrEqual : FormulaRelationOperator.LessThan,
                    values[1]));
            if (headConstant.Name == "HPow.hPow")
                return new ProjectionOutcome.Projected(new Formula.Power(values[0], values[1]));
            if (headConstant.Name == "HDiv.hDiv")
                return new ProjectionOutcome.Projected(new Formula.Fraction(values[0], values[1]));
            if (headConstant.Name is "HAdd.hAdd" or "HSub.hSub")
                return new ProjectionOutcome.Projected(new Formula.Binary(values[0],
                    headConstant.Name == "HAdd.hAdd" ? FormulaBinaryOperator.Add : FormulaBinaryOperator.Subtract, values[1]));
            if (leaf == "Eq" && values.Length >= 2) return new ProjectionOutcome.Projected(new Formula.Relation(values[^2], FormulaRelationOperator.Equal, values[^1]));
            if (leaf == "Ne" && values.Length >= 2) return new ProjectionOutcome.Projected(new Formula.Relation(values[^2], FormulaRelationOperator.NotEqual, values[^1]));
            if (leaf is "And" or "Or" or "Iff" && values.Length >= 2) return new ProjectionOutcome.Projected(new Formula.Logic(values[^2], leaf switch { "And" => FormulaLogicOperator.And, "Or" => FormulaLogicOperator.Or, _ => FormulaLogicOperator.Iff }, values[^1]));
            if (leaf == "Not" && values.Length == 1) return new ProjectionOutcome.Projected(new Formula.Not(values[0]));
            if (leaf == "norm" && values.Length == 1) return new ProjectionOutcome.Projected(new Formula.Norm(values[0]));
            if (leaf == "neg" && values.Length == 1) return new ProjectionOutcome.Projected(new Formula.Negate(values[0]));
            if (headConstant.Name == "OfNat.ofNat" && values.Length == 1) return new ProjectionOutcome.Projected(values[0]);
            if (headConstant.Name == "DFunLike.coe" && values.Length == 2)
                return new ProjectionOutcome.Projected(new Formula.Apply(values[0], [values[1]]));
            if (headConstant.Name == "HMul.hMul" && values.Length == 2)
                return new ProjectionOutcome.Projected(new Formula.Binary(values[0], FormulaBinaryOperator.Multiply, values[1]));
            if (headConstant.Name == "Membership.mem" && values.Length == 2)
                return new ProjectionOutcome.Projected(new Formula.Relation(values[1], FormulaRelationOperator.MemberOf, values[0]));
            if (leaf == "Exists" && semanticArguments.Length == 2 && semanticArguments[1] is LeanExpr.Lambda predicate)
            {
                var identifier = FormulaIdentifier.Create("x" + variables.Length);
                var domain = Project(semanticArguments[0], variables);
                var body = Project(predicate.Body, variables.Insert(0, new Formula.Symbol(identifier)));
                if (domain is ProjectionOutcome.Projected d && body is ProjectionOutcome.Projected b)
                    return new ProjectionOutcome.Projected(new Formula.Bind(FormulaQuantifier.Exists, identifier, d.Formula, b.Formula));
            }
            if (!TryNotation(headConstant.Name, out var notation))
                return new ProjectionOutcome.Unprojectable("constant:" + headConstant.Name);
            var canonical = new string(notation.Where(char.IsLetterOrDigit).ToArray());
            var functionFormula = new Formula.NamedConstant(FormulaIdentifier.Create(canonical));
            return values.Length == 0
                ? new ProjectionOutcome.Projected(functionFormula)
                : new ProjectionOutcome.Projected(new Formula.Apply(functionFormula, values.ToImmutableArray()));
        }
        return new ProjectionOutcome.Unprojectable(
            "unregistered-elaboration-shape:" + expression.GetType().Name);
    }

    private static bool TryNotation(string name, out string notation)
    {
        if (SemanticProjectionSignatures.Entries.TryGetValue(name, out var signature))
        {
            notation = signature.Notation;
            return true;
        }
        return ProjectionNotation.Entries.TryGetValue(name, out notation!)
            || ProjectionNotation.Entries.TryGetValue(name.Split('.').Last(), out notation!);
    }

    private static ProjectionOutcome ProjectDomain(LeanExpr expression, ImmutableArray<Formula> variables)
    {
        if (expression is LeanExpr.Metadata metadata) return ProjectDomain(metadata.Body, variables);
        if (expression is LeanExpr.Pi pi && !PropPiToImplicationRule.ContainsBoundVariable(pi.Body, 0))
        {
            var domain = ProjectDomain(pi.Domain, variables);
            var codomain = ProjectDomain(pi.Body, variables.Insert(0, new Formula.Placeholder()));
            if (domain is ProjectionOutcome.Unprojectable failure) return failure;
            if (codomain is ProjectionOutcome.Unprojectable other) return other;
            return new ProjectionOutcome.Projected(new Formula.TypeArrow(
                ((ProjectionOutcome.Projected)domain).Formula, ((ProjectionOutcome.Projected)codomain).Formula));
        }
        return Project(expression, variables);
    }

    private static ProjectionOutcome ProjectFunction(LeanExpr expression, ImmutableArray<Formula> variables)
    {
        if (expression is LeanExpr.Metadata metadata) return ProjectFunction(metadata.Body, variables);
        if (expression is LeanExpr.Let let) return ProjectFunction(Instantiate(let.Body, let.Value), variables);
        if (expression is not LeanExpr.Lambda lambda) return Project(expression, variables);
        var identifier = FormulaIdentifier.Create("x" + variables.Length);
        var domain = ProjectDomain(lambda.Domain, variables);
        var body = ProjectFunction(lambda.Body, variables.Insert(0, new Formula.Symbol(identifier)));
        if (domain is ProjectionOutcome.Unprojectable failure) return failure;
        if (body is ProjectionOutcome.Unprojectable other) return other;
        return new ProjectionOutcome.Projected(new Formula.LatexSequence([
            new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis),
            new Formula.LatexMacro(FormulaLatexMacro.LambdaLower), new Formula.LatexSpace(),
            new Formula.Symbol(identifier), new Formula.LatexSymbol(FormulaLatexSymbol.Colon),
            ((ProjectionOutcome.Projected)domain).Formula,
            new Formula.LatexSymbol(FormulaLatexSymbol.Period), new Formula.LatexSpace(),
            ((ProjectionOutcome.Projected)body).Formula,
            new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis)]));
    }

    // De Bruijn substitution removes the let slot and lifts free indices in its
    // value under each intervening binder, including dependent domains and lets.
    private static LeanExpr Instantiate(LeanExpr expression, LeanExpr value, uint depth = 0) => expression switch
    {
        LeanExpr.Bound bound when bound.Index == depth => Lift(value, depth),
        LeanExpr.Bound bound when bound.Index > depth => new LeanExpr.Bound(bound.Index - 1),
        LeanExpr.App app => new LeanExpr.App(Instantiate(app.Function, value, depth), Instantiate(app.Argument, value, depth)),
        LeanExpr.Lambda lambda => new LeanExpr.Lambda(lambda.BinderInfo,
            Instantiate(lambda.Domain, value, depth), Instantiate(lambda.Body, value, checked(depth + 1))),
        LeanExpr.Pi pi => new LeanExpr.Pi(pi.BinderInfo,
            Instantiate(pi.Domain, value, depth), Instantiate(pi.Body, value, checked(depth + 1))),
        LeanExpr.Let let => new LeanExpr.Let(let.Nondependent,
            Instantiate(let.Type, value, depth), Instantiate(let.Value, value, depth),
            Instantiate(let.Body, value, checked(depth + 1))),
        LeanExpr.Metadata metadata => new LeanExpr.Metadata(Instantiate(metadata.Body, value, depth)),
        LeanExpr.Projection projection => new LeanExpr.Projection(projection.Name, projection.Index,
            Instantiate(projection.Body, value, depth)),
        _ => expression
    };

    private static LeanExpr Lift(LeanExpr expression, uint amount, uint cutoff = 0) => expression switch
    {
        LeanExpr.Bound bound when bound.Index >= cutoff => new LeanExpr.Bound(checked(bound.Index + amount)),
        LeanExpr.App app => new LeanExpr.App(Lift(app.Function, amount, cutoff), Lift(app.Argument, amount, cutoff)),
        LeanExpr.Lambda lambda => new LeanExpr.Lambda(lambda.BinderInfo,
            Lift(lambda.Domain, amount, cutoff), Lift(lambda.Body, amount, checked(cutoff + 1))),
        LeanExpr.Pi pi => new LeanExpr.Pi(pi.BinderInfo,
            Lift(pi.Domain, amount, cutoff), Lift(pi.Body, amount, checked(cutoff + 1))),
        LeanExpr.Let let => new LeanExpr.Let(let.Nondependent,
            Lift(let.Type, amount, cutoff), Lift(let.Value, amount, cutoff),
            Lift(let.Body, amount, checked(cutoff + 1))),
        LeanExpr.Metadata metadata => new LeanExpr.Metadata(Lift(metadata.Body, amount, cutoff)),
        LeanExpr.Projection projection => new LeanExpr.Projection(projection.Name, projection.Index,
            Lift(projection.Body, amount, cutoff)),
        _ => expression
    };

    private static (LeanExpr Head, ImmutableArray<LeanExpr> Arguments) Flatten(LeanExpr expression)
    {
        var arguments = ImmutableArray.CreateBuilder<LeanExpr>();
        while (expression is LeanExpr.App app) { arguments.Insert(0, app.Argument); expression = app.Function; }
        return (expression, arguments.ToImmutable());
    }
}

internal static class StatementProjectionFixtureLoader
{
    internal const string ProjectorEpoch = "statement-projector-v1";
    internal sealed record Assessment(ProjectionOutcome Outcome, string DeclarationContentDigest);
    private static readonly AsyncLocal<string?> RepositoryRoot = new();
    private static readonly AsyncLocal<(string Root, Lazy<ImmutableDictionary<RepoPath, ImmutableArray<StatementEntry>>> Statements)?>
        FreshStatements = new();
    private static readonly Dictionary<string, ImmutableDictionary<RepoPath, ImmutableArray<StatementEntry>>> StatementsByRoot =
        new(StringComparer.Ordinal);
    private static readonly ConditionalWeakTable<Formula, LeanDeclarationRef> Derived = new();

    internal static Formula FromLean(LeanDeclarationRef declaration)
    {
        ArgumentNullException.ThrowIfNull(declaration);
        var formula = Assess(declaration).Outcome switch
        {
            ProjectionOutcome.Projected projected => projected.Formula,
            ProjectionOutcome.Unprojectable failed => throw new InvalidOperationException(
                $"Pinned statement-v1 fixture is unprojectable for {declaration.Value}: {failed.Reason}"),
            _ => throw new InvalidOperationException("Unknown statement projection outcome.")
        };
        RestoreDerived(formula, declaration);
        return formula;
    }

    internal static void RestoreDerived(Formula formula, LeanDeclarationRef declaration)
    {
        ArgumentNullException.ThrowIfNull(formula);
        ArgumentNullException.ThrowIfNull(declaration);
        Derived.Add(formula, declaration);
    }

    internal static bool IsDerivedFrom(Formula formula, LeanDeclarationRef declaration) =>
        Derived.TryGetValue(formula, out var source)
        && string.Equals(source.Value, declaration.Value, StringComparison.Ordinal);

    internal static ProjectionOutcome Project(LeanDeclarationRef declaration)
        => Assess(declaration).Outcome;

    internal static Assessment Assess(LeanDeclarationRef declaration)
    {
        ArgumentNullException.ThrowIfNull(declaration);
        var statements = StatementsForCurrentRepository();
        var matches = statements.TryGetValue(declaration.Reference.Path, out var module)
            ? module.Where(entry => string.Equals(
                entry.Name[(entry.Name.LastIndexOf('.') + 1)..], declaration.DeclarationName,
                StringComparison.Ordinal)).ToArray()
            : [];
        if (matches.Length != 1)
        {
            var reason = (matches.Length == 0 ? "missing:" : "ambiguous:") + declaration.Value;
            return new Assessment(
                new ProjectionOutcome.Unprojectable(reason),
                Convert.ToHexString(SHA256.HashData(Encoding.UTF8.GetBytes(reason))).ToLowerInvariant());
        }
        var entry = matches[0];

        // The projector projects the declaration's *type*. For a theorem the type is the proposition,
        // so projecting it restates nothing the author owns. For a def, an inductive, or a structure the
        // type is only the signature — the defining body never reaches the projector — so a projected
        // statement there would present a signature as if it were the definition. Judge those
        // unprojectable, which leaves the author free to state the definition and records the gap.
        // Kind and statement decoding apply only after selecting one declaration in its owner module.
        if (!string.Equals(entry.Kind, "theorem", StringComparison.Ordinal))
        {
            var reason = "non-propositional-declaration:" + entry.Kind;
            return new Assessment(new ProjectionOutcome.Unprojectable(reason),
                Convert.ToHexString(SHA256.HashData(Encoding.UTF8.GetBytes(reason))).ToLowerInvariant());
        }

        var encoded = entry.Type;
        var digest = Convert.ToHexString(SHA256.HashData(Encoding.UTF8.GetBytes(encoded))).ToLowerInvariant();
        try
        {
            return new Assessment(StatementProjector.Project(StatementV1Decoder.Decode(encoded).Type), digest);
        }
        catch (FormatException exception)
        {
            return new Assessment(new ProjectionOutcome.Unprojectable(
                "unregistered-elaboration-shape:statement-v1-decoder:" + exception.Message), digest);
        }
    }

    internal static string ReasonCode(string reason) => reason.Split(':', 2)[0];
    internal static string OffendingSubject(string reason) =>
        reason.Contains(':', StringComparison.Ordinal) ? reason[(reason.IndexOf(':') + 1)..] : reason;

    internal static string FixtureDirectory(string repositoryRoot) => Path.Combine(
        repositoryRoot, "Golden", "Projection");

    internal static T WithRepositoryRoot<T>(string repositoryRoot, Func<T> action)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(action);
        var previous = RepositoryRoot.Value;
        RepositoryRoot.Value = Path.GetFullPath(repositoryRoot);
        try
        {
            return action();
        }
        finally
        {
            RepositoryRoot.Value = previous;
        }
    }

    internal static T WithScriptRepositoryRoot<T>(string repositoryRoot, Func<T> action) =>
        FreshStatements.Value is { } fresh && fresh.Root == Path.GetFullPath(repositoryRoot)
            ? WithRepositoryRoot(repositoryRoot, action)
            : WithFreshRepositoryRoot(repositoryRoot, action);

    internal static T WithFreshRepositoryRoot<T>(string repositoryRoot, Func<T> action)
    {
        var root = Path.GetFullPath(repositoryRoot);
        var previous = FreshStatements.Value;
        FreshStatements.Value = (root, new Lazy<ImmutableDictionary<RepoPath, ImmutableArray<StatementEntry>>>(
            () => LoadStatements(root)));
        try { return WithRepositoryRoot(root, action); }
        finally { FreshStatements.Value = previous; }
    }

    private static ImmutableDictionary<RepoPath, ImmutableArray<StatementEntry>> StatementsForCurrentRepository()
    {
        var repositoryRoot = RepositoryRoot.Value ?? FindRepositoryRoot();
        if (FreshStatements.Value is { } fresh && fresh.Root == repositoryRoot)
            return fresh.Statements.Value;
        lock (StatementsByRoot)
        {
            if (!StatementsByRoot.TryGetValue(repositoryRoot, out var statements))
            {
                statements = LoadStatements(repositoryRoot);
                StatementsByRoot.Add(repositoryRoot, statements);
            }

            return statements;
        }
    }

    internal static ImmutableDictionary<RepoPath, ImmutableArray<StatementEntry>> LoadStatements(string repositoryRoot)
    {
        var fixtureDirectory = FixtureDirectory(repositoryRoot);
        var fixtures = new[]
        {
            (Name: "statement-projection-pilot-v1.json", Schema: "statement-projection-pilot-fixture-v1"),
            (Name: "statement-projection-expansion-v1.json", Schema: "statement-projection-expansion-fixture-v1")
        };
        var declarations = new Dictionary<(RepoPath SourcePath, string Name), StatementEntry>();
        foreach (var fixtureSpec in fixtures)
        {
            var path = Path.Combine(fixtureDirectory, fixtureSpec.Name);
            if (!File.Exists(path))
            {
                throw new FileNotFoundException(
                    $"Projection fixture is missing from repository {repositoryRoot}: {path}",
                    path);
            }
            using var fixture = JsonDocument.Parse(File.ReadAllBytes(path));
            var schema = fixture.RootElement.GetProperty("schema").GetString();
            if (!string.Equals(schema, fixtureSpec.Schema, StringComparison.Ordinal))
                throw new FormatException($"Projection fixture schema mismatch: {path}");
            foreach (var declaration in fixture.RootElement.GetProperty("declarations").EnumerateArray())
            {
                var name = declaration.GetProperty("name").GetString()
                    ?? throw new FormatException($"Projection fixture has a null declaration name: {path}");
                if (!declaration.TryGetProperty("source_path", out var sourceElement)
                    || sourceElement.ValueKind != JsonValueKind.String
                    || !RepoPath.TryCreate(sourceElement.GetString(), out var sourcePath)
                    || !sourcePath.Value.EndsWith(".lean", StringComparison.Ordinal))
                    throw new FormatException($"Projection fixture declaration has a missing or invalid source_path: {name}");
                var statement = declaration.GetProperty("type").GetString()
                    ?? throw new FormatException($"Projection fixture has a null statement-v1 value: {name}");
                // Pins supply the entire projection corpus in every environment; kind is required
                // because only theorem types can supply a statement presentation.
                var kind = declaration.TryGetProperty("kind", out var kindElement)
                    ? kindElement.GetString()
                    : throw new FormatException($"Projection fixture declaration has no kind: {name}");
                if (string.IsNullOrEmpty(kind))
                    throw new FormatException($"Projection fixture declaration has an empty kind: {name}");
                if (!declarations.TryAdd((sourcePath, name), new StatementEntry(name, sourcePath, statement, kind)))
                    throw new FormatException($"Duplicate projection fixture declaration: {name} ({sourcePath.Value})");
            }
        }
        return declarations.Values.GroupBy(static entry => entry.SourcePath)
            .ToImmutableDictionary(static group => group.Key, static group => group.ToImmutableArray());
    }

    private static string FindRepositoryRoot()
    {
        for (var directory = new DirectoryInfo(Environment.CurrentDirectory);
             directory is not null;
             directory = directory.Parent)
        {
            if (File.Exists(Path.Combine(directory.FullName, "global.json"))
                && Directory.Exists(Path.Combine(directory.FullName, "Golden", "Projection")))
                return directory.FullName;
        }
        throw new DirectoryNotFoundException(
            "Could not locate repository root containing Golden/Projection statement fixtures.");
    }
}

internal sealed record StatementEntry(string Name, RepoPath SourcePath, string Type, string Kind);
