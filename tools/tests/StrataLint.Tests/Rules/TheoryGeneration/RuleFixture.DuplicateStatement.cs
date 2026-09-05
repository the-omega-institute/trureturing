using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal sealed partial class RuleFixture
{
    internal const string DuplicateLeftGid = "D5/S0/Carrier/DuplicateLeft";
    internal const string DuplicateRightGid = "D5/S1/Phase/DuplicateRight";
    internal const string DuplicateStatementType = "statement-v1(uparams=[],type=ec(Fixture.Dup,[]))";
    internal const string DistinctStatementType = "statement-v1(uparams=[],type=ec(Fixture.Other,[]))";

    // A statement-carrying module the duplicate-statement advisory can see: the
    // snapshot text only has to satisfy the header and address rules, while the
    // declaration the advisory reads comes from the Lean report.
    internal void AddStatementModule(
        string gid,
        string declarationName,
        string typeRepresentation,
        string kind = "theorem",
        bool includeInStatement = true,
        bool touched = false)
    {
        var path = gid + ".lean";
        var text = HeaderFor(gid, "E") + $"{kind} fixtureStatement : Fixture.Dup := by trivial\n";
        Files[path] = text;
        Baseline[path] = text;
        ForkPoint[path] = text;
        var declaration = new LeanDeclaration(
            declarationName,
            kind,
            typeRepresentation,
            ImmutableArray<string>.Empty)
        {
            IncludeInStatement = includeInStatement,
        };
        Reports[path] = Report(declarations: [declaration]);
        BaselineReports[path] = Reports[path];
        if (touched)
        {
            Changes.Add(path);
        }
    }

    // The default fixture's digestion entry covers D5/S0/Carrier/BackfillTarget, so
    // SL-016 blocks until that module exists. Any fixture judged by the whole active
    // catalog needs it; the theorist fixture carries its own copy for the same reason.
    internal void AddDigestionCoverageTarget()
    {
        const string gid = "D5/S0/Carrier/BackfillTarget";
        var path = gid + ".lean";
        var text = HeaderFor(gid, "G") + "def duplicateBackfillTargetFixture : Unit := ()\n";
        Files[path] = text;
        Baseline[path] = text;
        ForkPoint[path] = text;
        Reports[path] = Report();
        BaselineReports[path] = Report();
    }
}
