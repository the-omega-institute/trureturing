using Dunet;

namespace StrataLint.Engine;

[Union(EnableImplicitConversions = false)]
internal partial record ReceiptApplicability
{
    public partial record Required;
    public partial record NotApplicableNonFormal;
    public partial record NotApplicableMirrorWaiver;
    public partial record PendingTarget;
    public partial record Failure(string Message);

    internal string? ObservationCode => this switch
    {
        Required => null,
        NotApplicableNonFormal => "scribe-not-applicable:non-formal",
        NotApplicableMirrorWaiver => "scribe-not-applicable:mirror-waiver",
        PendingTarget => "scribe-pending-target",
        Failure => null,
        _ => throw new InvalidOperationException("Unknown receipt applicability."),
    };

    internal static ReceiptApplicability Classify(
        Gid? gid,
        CurrentEdgeValidation edge,
        RepositorySnapshot snapshot,
        LeanAxiomReport? report,
        FrozenStatementIndex? frozen)
    {
        if (gid is null) return new Failure("unparsable coverage GID");
        switch (gid.ToTarget())
        {
            case Target.Blueprint or Target.Evidence or Target.Chronicle or Target.Library or Target.Paper:
                return new NotApplicableNonFormal();
            case Target.Formal formal:
                if (!snapshot.TryGetFile(formal.Path.Value, out var module)
                    || !RepositoryRules.TryHeader(module.Text, out var header))
                    return new Failure("missing or malformed live Lean header");
                if (!RepositoryRules.TryMirror(header.MirrorB, "D5/B/", out var mirror, out var mirrorError))
                    return new Failure("mirror-B " + mirrorError);
                if (report is null || !report.Files.TryGetValue(formal.Path, out var moduleReport)
                    || !string.IsNullOrEmpty(moduleReport.Error))
                    return new Failure("current Lean report is unavailable");
                if (frozen is null) return new Failure("current frozen authority is unavailable");

                if (!edge.IsResolved)
                {
                    // Unresolved catalog membership/selectors are pending; an unreadable
                    // authority is not evidence that a target is pending.
                    if (!frozen.ContainsModule(formal.Path)) return new PendingTarget();
                    if (!frozen.TryResolve(gid, out _, out var error, out var failure)
                        && failure is FrozenStatementResolutionFailure.MissingDeclaration
                            or FrozenStatementResolutionFailure.AmbiguousDeclaration)
                        return new PendingTarget();
                    return new Failure(error.Length > 0 ? error : edge.Diagnostic);
                }

                if (!edge.IsClosed) return new PendingTarget();
                return mirror is null ? new NotApplicableMirrorWaiver() : new Required();
            default:
                return new Failure("unknown coverage target plane");
        }
    }
}
