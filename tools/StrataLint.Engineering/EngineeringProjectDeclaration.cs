namespace StrataLint.Engineering;

internal sealed record EngineeringProjectOwner(string Path, string Assembly);

// Data needed by topology and the base execution floor. Policy owned by other
// consumers (Compile, namespace, execution reuse) is deliberately absent.
internal record EngineeringProjectDeclaration(
    string Path,
    string Assembly,
    string Role,
    string[] References,
    EngineeringProjectOwner? Owner,
    string? OwnedTestAssembly,
    string? TestPartition)
{
    internal bool IsTest => Role is "owned-test" or "cross-cutting-test";
}

internal sealed record EngineeringProjectRegistration(
    string Path,
    string Assembly,
    string Role,
    string[] Include,
    string[] Exclude,
    string[] References,
    EngineeringProjectOwner? Owner,
    string? OwnedTestAssembly,
    string? TestPartition,
    string RootNamespace,
    string[] NamespaceExclude,
    string[] GlobalNamespaceExceptions)
    : EngineeringProjectDeclaration(Path, Assembly, Role, References, Owner, OwnedTestAssembly, TestPartition);

internal sealed record EngineeringProjectManifest(
    int Version,
    EngineeringProjectRegistration[] Projects,
    EngineeringProjectRegistration[] HistoricalProjects,
    string[] RuleBuildInputs);
