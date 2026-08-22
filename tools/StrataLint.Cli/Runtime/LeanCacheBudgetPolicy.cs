namespace StrataLint.Cli;

internal static class LeanCacheBudgetPolicy
{
    /// policy-override (CLAUDE.md 第Ⅵ节「量腹而食」第三型) — 2026-08-20.
    ///
    /// THIS IS NOT A DERIVED VALUE. It is a declared override, not `capacity-derived`
    /// and not `relation-derived`; it is not a function of vCPU, memory, or any other
    /// machine capacity, and it must not be presented as one.
    ///
    /// Domain: every process this budget is passed to, which is more than the build.
    /// It bounds the `cp -R` that clones the donor cache, `lake exe cache get`, and —
    /// through `CommandBudget` — the one arbitrary command
    /// `LeanCacheEnsureCommand` runs for `worktree with-cache-writer`, which in this
    /// repository is `lake build` from the Makefile and both the `lake build` and the
    /// `lake env lean --run Inspector.lean` that `tools/lean-inspector/inspect.sh`
    /// passes. A number chosen against the build alone therefore also lengthens how long
    /// a hung `cp` or a stalled cache fetch is tolerated; that is accepted here as the
    /// cost of the triage. Deliberately no line numbers: an earlier version of this
    /// comment carried five line references, and the three that pointed into this file
    /// were copied from the pre-insertion text. Inserting the comment moved each of those
    /// three targets down twelve lines, so all three were false the moment they were
    /// committed. (The two cross-file references were still correct; the point is that a
    /// local anchor cannot survive its own comment.)
    /// Out of domain: the `dotnet restore` timeout in `WorktreeCommand`, a separate knob
    /// that merely happened to carry the same literal and is not touched here.
    ///
    /// Positive readings — ElonSG only, 2026-08-20; ANOTHER MACHINE MUST REMEASURE, and
    /// none of these numbers is reproducible from this repository, so they are this
    /// author's reported measurements rather than committed evidence. Building the
    /// single most expensive subgraph — `S0/Tower/TribonacciPeriodicElevenDistinct/
    /// {PartB..PartF}` with `S0/Tower/NodupAssembly/PeriodEleven` — took 1656s on the
    /// main checkout and 1212s on a lane, both `LAKE_RC=0`. Those modules landed
    /// 2026-08-18, so this ceiling first became reachable two days before this override.
    ///
    /// Negative readings — same machine, same day, same caveat. `make lean-report`
    /// returned `EXIT=2` with `lake timed out after 1800 seconds` twice in a row. The
    /// second failure needed only three remaining modules, which is the load-bearing
    /// observation: the wall is struck by individual expensive subgraphs, not by module
    /// count. The slack left under the old ceiling was (1800 - 1656) / 1800 = 8%, and
    /// concurrent load from other drivers on this machine was observed holding CPU idle
    /// at 0% for over 25 minutes, which consumes that slack outright.
    ///
    /// Value: 3600s is a chosen round hour, NOT a derivation. It has to clear the
    /// measured 1656s with room for the contention above, and it is half the ceiling
    /// this knob's existing escape hatch already sanctions (`Math.Clamp(..., 300, 7200)`
    /// below), so it widens no bound that was not already permitted. Any ratio one can
    /// compute against 1656 is arithmetic after the fact, not a rule that produced this
    /// number; do not read one into it.
    ///
    /// Case: https://github.com/the-omega-institute/trureturing/issues/2535
    /// Owner: repository owner (directed 2026-08-20 as triage while the durable cache
    /// fix proceeds separately on macstudio-4).
    /// NOT PERMANENT. Exit condition: retire this override once the machine-level D5
    /// build cache lands, because a lane that clones a complete cache never pays this
    /// build at all; or replace it with a genuine derivation whose independent variable
    /// includes the cost of the most expensive single subgraph, not machine capacity
    /// alone — a capacity-derived value that ignores that term is struck by one module
    /// no matter how wide it is.
    internal const int DefaultProvisionBudgetSeconds = 3600;
}
