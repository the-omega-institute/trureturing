using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class PapergenCommandTests
{
    /// Positive floor for the two membership negatives. Carrier A is the actively frozen node and
    /// the recipe names its frozen declaration, so validation must succeed. Without this, an
    /// implementation that rejects every declaration whenever a ledger is present would satisfy
    /// the negatives and keep the pre-ledger behaviour as a forbidden compatibility bypass.
    [Fact]
    public void ValidatorAcceptsDeclarationsCarriedByTheActiveFrozenNode()
    {
        using var repository = CarrierLedgerRepository(
            FrozenCarrierA,
            ["D5/S0/Carrier/A.a"],
            "D5/B/S0/Carrier/A");

        var outcome = PaperRecipeValidator.Validate(repository.Path, repository.Gateway, repository.Reports, "D5-P001");

        var valid = Assert.IsType<PaperRecipeValidationOutcome.Valid>(outcome);
        Assert.Equal("D5-P001", valid.Recipe.Id);
        Assert.Single(valid.Recipe.Declarations);
    }

    /// One declaration is carried by the active node and one is not. Membership must hold for
    /// every declaration, so an implementation that accepts on any match — or that inspects only
    /// the first entry — stays red here while both single-declaration cases would pass it.
    [Fact]
    public void ValidatorRejectsRecipesMixingActiveAndUnfrozenDeclarations()
    {
        using var repository = CarrierLedgerRepository(
            FrozenCarrierA,
            ["D5/S0/Carrier/A.a", "D5/S0/Carrier/B.b"],
            "D5/B/S0/Carrier/A",
            unfrozen: ("B", "namespace D5.S0.Carrier.B\n\ntheorem b : True := by trivial\n\nend D5.S0.Carrier.B\n"));

        var outcome = PaperRecipeValidator.Validate(repository.Path, repository.Gateway, repository.Reports, "D5-P001");

        var invalid = Assert.IsType<PaperRecipeValidationOutcome.Invalid>(outcome);
        Assert.Contains("D5/S0/Carrier/B.b", invalid.Message, StringComparison.Ordinal);
        Assert.Contains("not an active frozen declaration", invalid.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("D5/S0/Carrier/A.a", invalid.Message, StringComparison.Ordinal);
    }

    /// The Freeze event for carrier A stays in ledger history, but revocation removes its node
    /// from the active view. An implementation that scans historical Freeze payloads instead of
    /// FrozenLedgerConsistent.ActiveFrozenNodes would still find A here and wrongly certify it.
    [Fact]
    public void ValidatorRejectsDeclarationsWhoseNodeHasBeenRevoked()
    {
        using var repository = CarrierLedgerRepository(
            FrozenCarrierA,
            ["D5/S0/Carrier/A.a"],
            "D5/B/S0/Carrier/A",
            revokeFrozenNode: true);

        var outcome = PaperRecipeValidator.Validate(repository.Path, repository.Gateway, repository.Reports, "D5-P001");

        var invalid = Assert.IsType<PaperRecipeValidationOutcome.Invalid>(outcome);
        Assert.Contains("D5/S0/Carrier/A.a", invalid.Message, StringComparison.Ordinal);
        Assert.Contains("not an active frozen declaration", invalid.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("target file is missing", invalid.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("Lean declaration is missing", invalid.Message, StringComparison.Ordinal);
    }

    /// Two modules are frozen and the recipe names the second one's declaration. Every other
    /// fixture carries a single active node, so an implementation reading ActiveFrozenNodes[0]
    /// -- or otherwise consulting a single node -- passes all of them; here it rejects a
    /// legitimately frozen declaration.
    [Fact]
    public void ValidatorAcceptsDeclarationsCarriedByANodeOtherThanTheFirst()
    {
        using var repository = CarrierLedgerRepository(
            FrozenCarrierA,
            ["D5/S0/Carrier/C.c"],
            "D5/B/S0/Carrier/C",
            alsoFrozen: FrozenLedgerTestData.Module(
                "C",
                opaqueNameKeys: true,
                source: "namespace D5.S0.Carrier.C\n\ntheorem c : True := by trivial\n\nend D5.S0.Carrier.C\n"));

        var outcome = PaperRecipeValidator.Validate(
            repository.Path,
            repository.Gateway,
            repository.Reports,
            "D5-P001");

        var valid = Assert.IsType<PaperRecipeValidationOutcome.Valid>(outcome);
        Assert.Single(valid.Recipe.Declarations);
    }

    /// One node carries several declarations and the recipe names one that does not sort first.
    /// Every other fixture gives each module exactly one declaration, so an implementation that
    /// stops at DeclarationStatementIds[0] satisfies them all; here it rejects a frozen
    /// declaration.
    [Fact]
    public void ValidatorAcceptsDeclarationsBeyondTheFirstOnANode()
    {
        using var repository = CarrierLedgerRepository(
            FrozenLedgerTestData.Module(
                "A",
                opaqueNameKeys: true,
                source: "namespace D5.S0.Carrier.A\n\ntheorem a : True := by trivial\n\n"
                    + "theorem zeta : True := by trivial\n\nend D5.S0.Carrier.A\n",
                declarations: ["a", "zeta"]),
            ["D5/S0/Carrier/A.zeta"],
            "D5/B/S0/Carrier/A");

        var outcome = PaperRecipeValidator.Validate(
            repository.Path,
            repository.Gateway,
            repository.Reports,
            "D5-P001");

        var valid = Assert.IsType<PaperRecipeValidationOutcome.Valid>(outcome);
        Assert.Single(valid.Recipe.Declarations);
    }

    /// Declaration names as they appear in the source on disk, so the report cannot drift from
    /// the tree it claims to describe.
    private static ImmutableArray<string> DeclarationsIn(string source) =>
        System.Text.RegularExpressions.Regex
            .Matches(source, @"(?m)^\s*theorem\s+([A-Za-z_][A-Za-z0-9_']*)")
            .Select(static match => match.Groups[1].Value)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();

    private static string EvidenceBlock(IReadOnlyList<string>? gids) =>
        gids is null || gids.Count == 0
            ? " []"
            : "\n" + string.Join("\n", gids.Select(static gid => "  - " + gid));

    /// The ledger is canonical and loads cleanly; only its hash chain is broken. The existing
    /// malformed case uses arbitrary JSON, which DagLedgerLoader rejects on shape alone, so an
    /// implementation that loads the ledger and replays events itself -- never calling
    /// ValidateHistoryPrefix -- passes it. This one it cannot.
    [Fact]
    public void ValidatorRejectsLedgersThatLoadButFailHistoryValidation()
    {
        using var repository = CarrierLedgerRepository(
            FrozenCarrierA,
            ["D5/S0/Carrier/A.a"],
            "D5/B/S0/Carrier/A",
            tamperLedgerChain: true);

        var outcome = PaperRecipeValidator.Validate(
            repository.Path,
            repository.Gateway,
            repository.Reports,
            "D5-P001");

        var invalid = Assert.IsType<PaperRecipeValidationOutcome.Invalid>(outcome);
        Assert.Contains("not an active frozen declaration", invalid.Message, StringComparison.Ordinal);
    }

    /// Reattestation replaces the node id while admission holds the declaration set constant.
    /// An implementation that resolves membership through the original Freeze event's node id
    /// rejects a declaration that is still perfectly frozen.
    [Fact]
    public void ValidatorAcceptsDeclarationsAfterTheirNodeIsReattested()
    {
        using var repository = CarrierLedgerRepository(
            FrozenCarrierA,
            ["D5/S0/Carrier/A.a"],
            "D5/B/S0/Carrier/A",
            reattestFrozenNode: true);

        var outcome = PaperRecipeValidator.Validate(
            repository.Path,
            repository.Gateway,
            repository.Reports,
            "D5-P001");

        Assert.True(outcome is PaperRecipeValidationOutcome.Valid, outcome.ToString());
    }

    /// The mirror image: revocation lands on the reattested node, so an implementation checking
    /// revocation against the original Freeze id sees an id that was never revoked and certifies
    /// a withdrawn declaration.
    [Fact]
    public void ValidatorRejectsDeclarationsRevokedAfterReattestation()
    {
        using var repository = CarrierLedgerRepository(
            FrozenCarrierA,
            ["D5/S0/Carrier/A.a"],
            "D5/B/S0/Carrier/A",
            revokeFrozenNode: true,
            reattestFrozenNode: true);

        var outcome = PaperRecipeValidator.Validate(
            repository.Path,
            repository.Gateway,
            repository.Reports,
            "D5-P001");

        var invalid = Assert.IsType<PaperRecipeValidationOutcome.Invalid>(outcome);
        Assert.Contains("D5/S0/Carrier/A.a", invalid.Message, StringComparison.Ordinal);
        Assert.Contains("not an active frozen declaration", invalid.Message, StringComparison.Ordinal);
    }

    /// The gateway answers without throwing, but the capability it returns covers nothing. An
    /// implementation that uses that capability must fail closed; one that calls the gateway for
    /// ceremony and then manufactures TrustedFrozenGitReferences from the scanned inputs itself
    /// sails through -- and no other test can tell the two apart, because on the ordinary fake
    /// the returned value and the manufactured one are the same object shape.
    [Fact]
    public void ValidatorConsumesTheCapabilityTheGatewayReturns()
    {
        using var repository = CarrierLedgerRepository(
            FrozenCarrierA,
            ["D5/S0/Carrier/A.a"],
            "D5/B/S0/Carrier/A");

        var outcome = PaperRecipeValidator.Validate(
            repository.Path,
            repository.NonCoveringGateway,
            repository.Reports,
            "D5-P001");

        Assert.IsType<PaperRecipeValidationOutcome.Invalid>(outcome);
    }

    /// One node is revoked and the recipe names a different, still-active one. Both revocation
    /// negatives point at the withdrawn node, so "reject whenever the ledger records any
    /// revocation at all" passes them; it fails here.
    [Fact]
    public void ValidatorAcceptsActiveDeclarationsWhenAnotherNodeIsRevoked()
    {
        using var repository = CarrierLedgerRepository(
            FrozenCarrierA,
            ["D5/S0/Carrier/C.c"],
            "D5/B/S0/Carrier/C",
            revokeFrozenNode: true,
            alsoFrozen: FrozenLedgerTestData.Module(
                "C",
                opaqueNameKeys: true,
                source: "namespace D5.S0.Carrier.C\n\ntheorem c : True := by trivial\n\nend D5.S0.Carrier.C\n"));

        var outcome = PaperRecipeValidator.Validate(
            repository.Path,
            repository.Gateway,
            repository.Reports,
            "D5-P001");

        Assert.True(outcome is PaperRecipeValidationOutcome.Valid, outcome.ToString());
    }

    /// Membership must be decided against the Lean report, not by replaying the ledger alone.
    [Fact]
    public void ValidatorConsumesTheLeanReportSource()
    {
        using var repository = CarrierLedgerRepository(
            FrozenCarrierA,
            ["D5/S0/Carrier/A.a"],
            "D5/B/S0/Carrier/A");

        PaperRecipeValidator.Validate(
            repository.Path,
            repository.Gateway,
            repository.Reports,
            "D5-P001");

        Assert.NotEqual(0, repository.Reports.LoadCount);
    }

    /// An unreadable Lean report is an infrastructure fault, not a verdict on the recipe, so it
    /// must exit 2 rather than 1. Without this, wrapping the whole preparation in a catch-all
    /// that returns Invalid -- which PapergenCommand maps to exit 1 -- satisfies every other case.
    [Fact]
    public void CliReportsInfrastructureWhenTheLeanReportIsUnavailable()
    {
        using var repository = CarrierLedgerRepository(
            FrozenCarrierA,
            ["D5/S0/Carrier/A.a"],
            "D5/B/S0/Carrier/A");
        var console = new BufferedConsole();

        var exit = CliApplication.Run(
            ["papergen", "validate", "D5-P001"],
            new ProductionCliEnvironment(repository.Path, repository.Gateway, repository.UnavailableReports),
            console);

        Assert.Equal(2, exit);
        Assert.Equal(string.Empty, console.Output);
        Assert.Contains("PAPERGEN_VALIDATE_INFRASTRUCTURE", console.Error, StringComparison.Ordinal);
    }

    /// Adding a declaration to a frozen module changes the module's statement identity, and
    /// history validation compares that identity before any single declaration is considered. So
    /// this is not a question about the added declaration: the frozen view no longer describes
    /// this repository, and nothing in it may be certified. (Source bytes alone do not do this --
    /// a pending reattestation whose statement identity is unchanged is still accepted.)
    ///
    /// This replaces an earlier pair that asserted the added declaration was rejected while the
    /// already-frozen one still validated. A faithful implementation cannot do that -- preparation
    /// rejects the whole ledger before any declaration is considered -- so the pair was asserting
    /// something unreachable, and its negative half would have passed for the wrong reason.
    [Fact]
    public void ValidatorRejectsEverythingWhenTheTreeNoLongerMatchesTheAttestation()
    {
        using var repository = CarrierLedgerRepository(
            FrozenCarrierA,
            ["D5/S0/Carrier/A.a"],
            "D5/B/S0/Carrier/A",
            currentSource: "namespace D5.S0.Carrier.A\n\ntheorem a : True := by trivial\n\n"
                + "theorem zzz : True := by trivial\n\nend D5.S0.Carrier.A\n");

        var outcome = PaperRecipeValidator.Validate(
            repository.Path,
            repository.Gateway,
            repository.Reports,
            "D5-P001");

        var invalid = Assert.IsType<PaperRecipeValidationOutcome.Invalid>(outcome);
        Assert.Contains(FrozenLedgerChangeClassifier.AcceptedRoot, invalid.Message, StringComparison.Ordinal);
    }

    /// The module carries `hidden` and it is in the Lean report, so ResolveSignature finds it --
    /// but CanonicalStatementWriter keeps only IncludeInStatement declarations, so the frozen node
    /// never recorded it. Membership therefore has to consult the node's declaration set: a lookup
    /// that stops at the RepoPath certifies a declaration the ledger does not carry, and passes
    /// every other case in this file.
    [Fact]
    public void ValidatorRejectsDeclarationsTheFrozenNodeExcludedFromItsStatements()
    {
        using var repository = CarrierLedgerRepository(
            FrozenLedgerTestData.Module(
                "A",
                opaqueNameKeys: true,
                source: "namespace D5.S0.Carrier.A\n\ntheorem a : True := by trivial\n\n"
                    + "theorem hidden : True := by trivial\n\nend D5.S0.Carrier.A\n",
                declarations: ["a", "hidden"],
                excluded: ["hidden"]),
            ["D5/S0/Carrier/A.hidden"],
            "D5/B/S0/Carrier/A",
            excludedDeclarations: ["hidden"]);

        var outcome = PaperRecipeValidator.Validate(
            repository.Path,
            repository.Gateway,
            repository.Reports,
            "D5-P001");

        var invalid = Assert.IsType<PaperRecipeValidationOutcome.Invalid>(outcome);
        Assert.Contains("D5/S0/Carrier/A.hidden", invalid.Message, StringComparison.Ordinal);
        Assert.Contains("not an active frozen declaration", invalid.Message, StringComparison.Ordinal);
    }

    /// A report that parses to nothing useful is still infrastructure, not a verdict about the
    /// recipe. It raises the same FormatException type the ledger path raises, so folding the two
    /// together would report a build-artefact fault as a rejected paper.
    [Fact]
    public void CliReportsInfrastructureWhenTheLeanReportIsMalformed()
    {
        using var repository = CarrierLedgerRepository(
            FrozenCarrierA,
            ["D5/S0/Carrier/A.a"],
            "D5/B/S0/Carrier/A");
        var console = new BufferedConsole();

        var exit = CliApplication.Run(
            ["papergen", "validate", "D5-P001"],
            new ProductionCliEnvironment(repository.Path, repository.Gateway, repository.MalformedReports),
            console);

        Assert.Equal(2, exit);
        Assert.Equal(string.Empty, console.Output);
        Assert.Contains("PAPERGEN_VALIDATE_INFRASTRUCTURE", console.Error, StringComparison.Ordinal);
    }

    /// A report whose bytes are not valid UTF-8 fails in the decoder, before anything becomes a
    /// FormatException. It is still a build-artefact fault, and it must be reported by papergen
    /// rather than falling through to the CLI's generic handler.
    [Fact]
    public void CliReportsInfrastructureWhenTheLeanReportIsNotDecodable()
    {
        using var repository = CarrierLedgerRepository(
            FrozenCarrierA,
            ["D5/S0/Carrier/A.a"],
            "D5/B/S0/Carrier/A");
        var console = new BufferedConsole();

        var exit = CliApplication.Run(
            ["papergen", "validate", "D5-P001"],
            new ProductionCliEnvironment(repository.Path, repository.Gateway, repository.UndecodableReports),
            console);

        Assert.Equal(2, exit);
        Assert.Contains("PAPERGEN_VALIDATE_INFRASTRUCTURE", console.Error, StringComparison.Ordinal);
    }

    /// A ledger that is there but cannot be opened is the environment refusing to let us look, not
    /// this repository being wrong: spec A16 splits exit 1 (a violation) from exit 2
    /// (infrastructure), and nothing about the content has been observed. Contrast
    /// CliRejectsValidationWhenTheFrozenLedgerIsAbsent, where absence itself is the observation
    /// and exit 1 is right. Holding it exclusively is portable;
    /// changing its mode is not.
    [Fact]
    public void CliReportsInfrastructureWhenTheFrozenLedgerCannotBeOpened()
    {
        using var repository = CarrierLedgerRepository(
            FrozenCarrierA,
            ["D5/S0/Carrier/A.a"],
            "D5/B/S0/Carrier/A");
        var console = new BufferedConsole();

        using (new FileStream(
            Directory.EnumerateFiles(
                Path.Combine(repository.Path, FrozenLedgerChangeClassifier.AcceptedRoot)).First(),
            FileMode.Open,
            FileAccess.Read,
            FileShare.None))
        {
            var exit = CliApplication.Run(
                ["papergen", "validate", "D5-P001"],
                new ProductionCliEnvironment(repository.Path, repository.Gateway, repository.Reports),
                console);

            Assert.Equal(2, exit);
            Assert.Contains("PAPERGEN_VALIDATE_INFRASTRUCTURE", console.Error, StringComparison.Ordinal);
        }
    }


    /// The report loads and parses but does not describe the managed files in this tree, so it is
    /// closure validation inside preparation that rejects it. That is a second exit for a report
    /// fault, and it used to be reported as a ledger verdict at exit 1.
    [Fact]
    public void CliReportsInfrastructureWhenTheLeanReportDoesNotDescribeTheTree()
    {
        using var repository = CarrierLedgerRepository(
            FrozenCarrierA,
            ["D5/S0/Carrier/A.a"],
            "D5/B/S0/Carrier/A");
        var console = new BufferedConsole();

        var exit = CliApplication.Run(
            ["papergen", "validate", "D5-P001"],
            new ProductionCliEnvironment(repository.Path, repository.Gateway, repository.IncoherentReports),
            console);

        Assert.Equal(2, exit);
        Assert.Contains("PAPERGEN_VALIDATE_INFRASTRUCTURE", console.Error, StringComparison.Ordinal);
    }

    /// A repository that cannot be read is the environment failing, not this repository being
    /// wrong about its frozen ledger. Both arrive as the same exception types, so the failure has
    /// to be marked where it happens for the command to tell them apart.
    [Fact]
    public void CliReportsInfrastructureWhenTheRepositoryCannotBeRead()
    {
        using var repository = CarrierLedgerRepository(
            FrozenCarrierA,
            ["D5/S0/Carrier/A.a"],
            "D5/B/S0/Carrier/A");
        var console = new BufferedConsole();

        var exit = CliApplication.Run(
            ["papergen", "validate", "D5-P001"],
            new ProductionCliEnvironment(repository.Path, repository.UnreadableGateway, repository.Reports),
            console);

        Assert.Equal(2, exit);
        Assert.Contains("PAPERGEN_VALIDATE_INFRASTRUCTURE", console.Error, StringComparison.Ordinal);
    }

    /// The gateway read succeeds here and the bytes it returns are what will not decode, so a
    /// marker wrapped only around the gateway call leaves this failure unclassified. Spec A16 puts
    /// snapshot rejection in infrastructure; without the classification at the decode itself this
    /// arrives as an ordinary InvalidOperationException and the command reports exit 1 instead.
    [Fact]
    public void CliReportsInfrastructureWhenTheSnapshotCannotBeDecoded()
    {
        using var repository = CarrierLedgerRepository(
            FrozenCarrierA,
            ["D5/S0/Carrier/A.a"],
            "D5/B/S0/Carrier/A");
        var console = new BufferedConsole();

        var exit = CliApplication.Run(
            ["papergen", "validate", "D5-P001"],
            new ProductionCliEnvironment(repository.Path, repository.UndecodableGateway, repository.Reports),
            console);

        Assert.Equal(2, exit);
        Assert.Contains("PAPERGEN_VALIDATE_INFRASTRUCTURE", console.Error, StringComparison.Ordinal);
    }
}
