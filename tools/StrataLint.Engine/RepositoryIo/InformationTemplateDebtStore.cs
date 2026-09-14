using System.Collections.Immutable;

namespace StrataLint.Engine;

public sealed record InformationOccurrenceKey(
    string Root, string RegistrationModule, string Theorem, string ObjectArena, string Catalog);

public sealed record InformationTemplateContentInput(string Path, string Sha256);

public sealed record InformationTemplateDebtRow(
    InformationOccurrenceKey Key,
    string SeedBase,
    string StatementIdentity,
    string RegistrationSourceSha256,
    ImmutableArray<InformationTemplateContentInput> ContentInputs);

public sealed record InformationTemplateActivation(string SeedBase, bool Activated);

public static class InformationTemplateDebtStore
{
    public const string Root = "Golden/InformationTemplateDebt/";
    public const string ActivationPath = Root + "activation.json";

    public static string PathFor(InformationOccurrenceKey key) =>
        throw new FormatException("DTR-DebtSchema: key encoder unavailable");

    public static InformationTemplateDebtRow ReadRow(
        string path, ReadOnlySpan<byte> bytes, string authorizedSeed,
        RepositorySnapshot seedInputs) =>
        throw new FormatException("DTR-DebtSchema: checked loader unavailable");

    public static ImmutableArray<byte> WriteRow(InformationTemplateDebtRow row) =>
        throw new FormatException("DTR-DebtSchema: canonical encoder unavailable");

    public static InformationTemplateActivation ReadActivation(RepositorySnapshot protectedBase) =>
        throw new FormatException("DTR-Activation: protected activation unavailable");
}
