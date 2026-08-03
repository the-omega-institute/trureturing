using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace StrataLint.ArchitectureTests;

/// A tripwire, not a proof. Papergen decides whether a recipe's declarations are carried by the
/// active frozen ledger, and that answer is supposed to come from one place -- the preparation step
/// that loads, validates and projects the ledger. An implementation that rebuilt the answer from
/// the ledger machinery would return identical verdicts, so no behaviour test can see it. This
/// catches the cheap and likely form of that regression and nothing more.
///
/// EXACTLY WHAT IS CHECKED. Starting from Papergen's sources, follow simple type names written as
/// IdentifierNameSyntax; resolve each against type declarations found by name in the
/// StrataLint.Cli source tree; walk their declaration bodies; stop at DagLedgerCommandPreparation.
/// Report any listed replay type named anywhere along that walk.
///
/// KNOWN GAPS -- green here does NOT mean the machinery is unreachable.
///
/// Not seen because the syntax carries no matching name: extension method calls (the call site
/// names only the method), generic names (GenericNameSyntax is a different node and is not
/// collected), file-level using aliases, and a call to another member of the same type, which
/// names no type at all and so never leaves the declaration it started in.
///
/// Not seen because the source is not read, or not read the way the compiler reads it: helpers
/// declared in another assembly (Engine grants InternalsVisibleTo to this one, and a name
/// resolving nowhere in the CLI tree simply ends the walk); code inside regions the parser leaves
/// disabled, since ParseText uses default preprocessor symbols and a reference under a symbol such
/// as DEBUG stays disabled trivia; and linked or generated compilation inputs that are not files
/// under the scanned directories. Partial declarations are collected wherever their parts sit, so
/// a part in another directory is followed -- but only once some name reaches that type.
///
/// Not decidable statically at all: reflection, dynamic, DI, an assembled type string, a replay
/// method added inside the terminal type (the walk stops at the whole type, not at its Prepare
/// member), and an implementation that reimplements the parsing and validation without naming any
/// listed type.
///
/// Symbol binding across the solution would close the first group and most of the second. It would
/// not close the third, and for interface or virtual calls it resolves the declared member rather
/// than the runtime implementation. The unbounded constraint stays review-guarded and tracked.
internal static class PapergenLedgerReferenceTripwire
{
    /// The machinery that builds ledger authority from raw material. Capability types
    /// (FrozenLedgerConsistent, FrozenNodeMaterial, LeanAxiomReport) are deliberately absent:
    /// consuming an authority someone else established is the whole point. So is
    /// FrozenLedgerChangeClassifier, which only names where the ledger lives -- that constant is
    /// itself the single source of that path, and listing it would push Papergen into hardcoding
    /// the string instead.
    internal static readonly ImmutableArray<string> LedgerReplayTypes =
    [
        "AcyclicTruthDag",
        "DagLedgerLoader",
        "FrozenContentAddress",
        "FrozenLedger",
        "FrozenLedgerGenerator",
        "FrozenLedgerMaterializer",
        "LeanClosureValidator",
        "RawLeanReportArtifact",
        "SnapshotDecoder",
    ];

    /// Where the walk stops. This type names the machinery legitimately, on everyone's behalf.
    /// Stopping at the whole type rather than at its Prepare method is a known gap, listed above.
    internal static readonly ImmutableArray<string> WalkTerminals =
    [
        "DagLedgerCommandPreparation",
    ];

    internal static string CliDirectory(string repositoryRoot) => Path.Combine(
        repositoryRoot,
        "Meta",
        "StrataLint",
        "StrataLint.Cli");

    internal static string PapergenDirectory(string repositoryRoot) =>
        Path.Combine(CliDirectory(repositoryRoot), "Commands", "Papergen");

    /// Reported as "origin: symbol", so a failure names where the reference is rather than only
    /// that one exists. Syntax identifiers only: a comment or string that mentions a listed type is
    /// not a reference to it, and this boundary is documented in prose inside the sources it
    /// constrains.
    internal static string[] NamedReplayTypes(string cliDirectory, string papergenDirectory)
    {
        var declarations = Declarations(cliDirectory);
        var listed = LedgerReplayTypes.ToHashSet(StringComparer.Ordinal);
        var terminals = WalkTerminals.ToHashSet(StringComparer.Ordinal);
        var findings = new List<string>();
        var pending = new Queue<TypeBody>();
        var seen = new HashSet<string>(StringComparer.Ordinal);
        foreach (var file in Sources(papergenDirectory))
        {
            pending.Enqueue(new TypeBody(Path.GetFileName(file), NamedIdentifiers(Root(file))));
        }

        while (pending.Count > 0)
        {
            var (origin, named) = pending.Dequeue();
            findings.AddRange(named
                .Where(listed.Contains)
                .Select(symbol => $"{origin}: {symbol}"));
            foreach (var symbol in named)
            {
                if (terminals.Contains(symbol) || !seen.Add(symbol)) continue;
                if (!declarations.TryGetValue(symbol, out var bodies)) continue;
                foreach (var body in bodies) pending.Enqueue(body);
            }
        }

        return [.. findings.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal)];
    }

    private static IEnumerable<string> Sources(string directory) => Directory
        .EnumerateFiles(directory, "*.cs", SearchOption.AllDirectories)
        .Order(StringComparer.Ordinal);

    private static SyntaxNode Root(string file) =>
        CSharpSyntaxTree.ParseText(File.ReadAllText(file)).GetRoot();

    /// Keyed by type name, and scoped to each declaration's own body rather than to the file
    /// holding it. A file is the wrong unit: ILeanReportSource is a one-method interface that
    /// happens to sit beside the composition root, and following the file would drag in every
    /// command the root names -- reporting the whole CLI instead of what Papergen writes down.
    /// Partial declarations contribute each of their parts.
    private static Dictionary<string, List<TypeBody>> Declarations(string cliDirectory)
    {
        var declarations = new Dictionary<string, List<TypeBody>>(StringComparer.Ordinal);
        foreach (var file in Sources(cliDirectory))
        {
            foreach (var declaration in Root(file).DescendantNodes().OfType<BaseTypeDeclarationSyntax>())
            {
                var name = declaration.Identifier.ValueText;
                if (!declarations.TryGetValue(name, out var bodies))
                {
                    declarations[name] = bodies = [];
                }

                bodies.Add(new TypeBody(
                    $"{Path.GetFileName(file)} ({name})",
                    NamedIdentifiers(declaration)));
            }
        }

        return declarations;
    }

    private static ImmutableArray<string> NamedIdentifiers(SyntaxNode node) =>
        [.. node.DescendantNodes()
            .OfType<IdentifierNameSyntax>()
            .Select(static identifier => identifier.Identifier.ValueText)
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)];

    private readonly record struct TypeBody(string Origin, ImmutableArray<string> Named);
}
