using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Text;

namespace StrataLint.Engine;

internal enum ScribeBindingStrategy
{
    Eager,
    Demand,
}

internal sealed record ScribeBindingEvent(
    string ProjectPath,
    string SourcePath,
    ScribeCallableIdentity Identity,
    TextSpan Span,
    MethodKind Kind)
{
    internal static ScribeBindingEvent Create(string projectPath, ScribeBoundCallable callable, IMethodSymbol symbol)
    {
        var normalized = ScribeCallableIndex.Normalize(symbol);
        return new(projectPath, callable.Path,
            new(normalized.ContainingAssembly.Identity.Name,
                DocumentationCommentId.CreateDeclarationId(normalized) ?? normalized.ToDisplayString()),
            callable.Syntax.Span, normalized.MethodKind);
    }
}

internal interface IScribeBindingRecorder
{
    void BindingEdges(ScribeBindingEvent callable);
    void ExpandingRelevance(ScribeBindingEvent callable);
}

internal sealed class ScribeDemandBindingSession
{
    private readonly IReadOnlyDictionary<ScribeBoundCallable, IMethodSymbol> symbolsByCallable;
    private readonly IReadOnlySet<string>? productionAssemblies;
    private readonly Func<ScribeBoundCallable, string> projectPathFor;
    private readonly Action<ScribeBoundCallable, IMethodSymbol> bindEdges;
    private readonly IScribeBindingRecorder? recorder;
    private readonly HashSet<ScribeBoundCallable> bound = [];

    internal ScribeDemandBindingSession(
        IEnumerable<ScribeBoundCallable> governedTestRoots,
        IReadOnlyDictionary<ScribeBoundCallable, IMethodSymbol> symbolsByCallable,
        IReadOnlySet<string>? productionAssemblies,
        Func<ScribeBoundCallable, string> projectPathFor,
        Action<ScribeBoundCallable, IMethodSymbol> bindEdges,
        IScribeBindingRecorder? recorder)
    {
        GovernedTestRoots = governedTestRoots;
        this.symbolsByCallable = symbolsByCallable;
        this.productionAssemblies = productionAssemblies;
        this.projectPathFor = projectPathFor;
        this.bindEdges = bindEdges;
        this.recorder = recorder;
    }

    private IEnumerable<ScribeBoundCallable> GovernedTestRoots { get; }

    internal void Bind()
    {
        var pending = new Queue<ScribeBoundCallable>(GovernedTestRoots);
        while (pending.TryDequeue(out var callable))
        {
            if (!bound.Add(callable)) continue;
            bindEdges(callable, symbolsByCallable[callable]);
            foreach (var target in callable.Targets) pending.Enqueue(target);
        }

        LimitProductionTargets();
    }

    private void LimitProductionTargets()
    {
        if (productionAssemblies is null) return;

        var production = bound.Where(callable => productionAssemblies.Contains(
                symbolsByCallable[callable].ContainingAssembly.Name))
            .ToHashSet();
        var predecessors = production.ToDictionary(
            static callable => callable,
            static _ => new List<ScribeBoundCallable>());
        foreach (var callable in production)
        foreach (var target in callable.Targets)
        {
            if (predecessors.TryGetValue(target, out var callers)) callers.Add(callable);
        }

        var relevant = new HashSet<ScribeBoundCallable>();
        var pending = new Queue<ScribeBoundCallable>();
        foreach (var callable in production)
        {
            if (callable.CompileTimeInputUniverses.Count == 0
                && (!callable.MentionsCompileTimeInputUniverse
                    || !callable.BindingUnknownReasons.Contains(TestMapUnknownReason.Other)))
            {
                continue;
            }

            relevant.Add(callable);
            pending.Enqueue(callable);
            RecordRelevance(callable);
        }

        while (pending.TryDequeue(out var target))
        {
            foreach (var predecessor in predecessors[target])
            {
                if (!relevant.Add(predecessor)) continue;
                pending.Enqueue(predecessor);
                RecordRelevance(predecessor);
            }
        }

        foreach (var callable in bound)
        {
            callable.Targets.RemoveWhere(target =>
                production.Contains(target) && !relevant.Contains(target));
        }
    }

    private void RecordRelevance(ScribeBoundCallable callable)
    {
        if (recorder is null) return;
        recorder.ExpandingRelevance(ScribeBindingEvent.Create(
            projectPathFor(callable),
            callable,
            symbolsByCallable[callable]));
    }
}
