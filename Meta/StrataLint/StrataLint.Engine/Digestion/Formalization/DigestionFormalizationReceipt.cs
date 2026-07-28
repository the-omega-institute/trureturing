using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

// The canonical declaration signature a formalizer pre-commits to *before* the
// proof lands: the WHAT of the atom, pinned as (name_key, kind, type). type is
// the load-bearing anti-Goodhart field — it is the exact Lean statement, so a
// post-proof swap of the theorem body (e.g. to `True`) changes it.
internal sealed record DigestionFormalizationSignature(
    string NameKey,
    string Kind,
    string Type);

// digestion-formalization-v1 receipt (spec §4a "pre-committed signature"). The
// formalizer (workflow step 1, or a manual PR-1) produces this receipt at
// delivery time — before/while proving — pinning atom_id -> primary declaration
// GID -> declaration signature, and binding the atom's content (cas_ref /
// raw_sha256). The digestion cover transaction (PR-2) then admits a declaration
// only when the deposited declaration's *current* signature equals the pinned
// signature, which is base-agnostic (no file-byte newness) and therefore survives
// the honest two-phase deposit while rejecting a post-proof statement swap.
//
// Deferred (§4b, recorded not silent): this receipt does NOT attest that the
// pre-committed signature itself is a faithful, non-hollow rendering of the
// natural-language atom. A hollow pre-commitment (`theorem t : True`) that is then
// deposited unchanged would pass signature-match. Guarding the pre-commitment's
// fidelity is the separate digestion-fidelity-attestation-v1 / multi-model
// consensus gate, which is out of scope for this block.
internal sealed record DigestionFormalizationReceipt(
    string AtomId,
    string PrimaryGid,
    DigestionFormalizationSignature Signature,
    string CasRef,
    string RawSha256)
{
    internal const string Schema = "digestion-formalization-v1";

    private static readonly ImmutableHashSet<string> RootFields = ImmutableHashSet.Create(
        StringComparer.Ordinal,
        "atom_id",
        "cas_ref",
        "precommitted_signature",
        "primary_gid",
        "raw_sha256",
        "schema");

    private static readonly ImmutableHashSet<string> SignatureFields = ImmutableHashSet.Create(
        StringComparer.Ordinal,
        "kind",
        "name_key",
        "type");

    internal static ImmutableArray<byte> Write(DigestionFormalizationReceipt receipt)
    {
        ArgumentNullException.ThrowIfNull(receipt);
        Validate(receipt);
        var material = new
        {
            atom_id = receipt.AtomId,
            cas_ref = receipt.CasRef,
            precommitted_signature = new
            {
                kind = receipt.Signature.Kind,
                name_key = receipt.Signature.NameKey,
                type = receipt.Signature.Type,
            },
            primary_gid = receipt.PrimaryGid,
            raw_sha256 = receipt.RawSha256,
            schema = Schema,
        };
        return StructuredCanonicalWriter.WriteJson(JsonSerializer.SerializeToElement(material));
    }

    // Fail-closed loader: a missing file, non-canonical JSON, a wrong schema tag,
    // any field outside the closed schema, an empty required field, a primary_gid
    // that does not select a declaration, or a non-canonical fingerprint all throw
    // FormatException. Modeled on ScribeEmissionAttestation.Load.
    internal static DigestionFormalizationReceipt Load(RepositorySnapshot snapshot, string relativePath)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentException.ThrowIfNullOrWhiteSpace(relativePath);
        if (!snapshot.TryGetFile(relativePath, out var file))
        {
            throw new FormatException($"digestion formalization receipt is missing: {relativePath}");
        }

        using var document = JsonDocument.Parse(file.Text);
        if (!StructuredCanonicalWriter.WriteJson(document.RootElement).AsSpan()
                .SequenceEqual(file.RawBytes.AsSpan()))
        {
            throw new FormatException($"{relativePath} is not canonical JSON");
        }

        RequireFields(document.RootElement, RootFields, "root");
        if (RequireString(document.RootElement, "schema") != Schema)
        {
            throw new FormatException($"schema must be {Schema}");
        }

        var signatureElement = document.RootElement.GetProperty("precommitted_signature");
        RequireFields(signatureElement, SignatureFields, "precommitted_signature");
        var receipt = new DigestionFormalizationReceipt(
            RequireString(document.RootElement, "atom_id"),
            RequireString(document.RootElement, "primary_gid"),
            new DigestionFormalizationSignature(
                RequireString(signatureElement, "name_key"),
                RequireString(signatureElement, "kind"),
                RequireString(signatureElement, "type")),
            RequireString(document.RootElement, "cas_ref"),
            RequireString(document.RootElement, "raw_sha256"));
        Validate(receipt);
        return receipt;
    }

    // Resolve a declaration's canonical signature (name_key/kind/type) from a raw
    // Lean report, using the same GID-selector matching as DigestionStatusEvaluator
    // (Name == selector, or Name ends with ".selector"). Shared by the emitter
    // (which pins the pre-committed signature) and cover (which checks the deposited
    // signature against the pin), so both read the WHAT from one place. A missing
    // module or a zero/multiple declaration match is a fail-closed FormatException.
    internal static DigestionFormalizationSignature ResolveSignature(Gid gid, LeanAxiomReport report)
    {
        ArgumentNullException.ThrowIfNull(report);
        if (gid.ToTarget() is not Target.Formal { Declaration: { } selector } formal)
        {
            throw new FormatException($"GID must select a Lean declaration: {gid.Value}");
        }

        if (!report.Files.TryGetValue(formal.Path, out var module) || !string.IsNullOrEmpty(module.Error))
        {
            throw new FormatException($"declaration is absent from the Lean report: {gid.Value}");
        }

        var suffix = "." + selector;
        var matches = module.Declarations
            .Where(candidate => string.Equals(candidate.Name, selector, StringComparison.Ordinal)
                || candidate.Name.EndsWith(suffix, StringComparison.Ordinal))
            .ToArray();
        if (matches.Length != 1)
        {
            throw new FormatException(
                $"declaration {gid.Value} resolves to {matches.Length} report declarations");
        }

        var declaration = matches[0];
        return new DigestionFormalizationSignature(
            declaration.NameKey,
            declaration.Kind,
            declaration.TypeRepresentation);
    }

    private static void Validate(DigestionFormalizationReceipt receipt)
    {
        if (string.IsNullOrWhiteSpace(receipt.AtomId)
            || string.IsNullOrWhiteSpace(receipt.PrimaryGid)
            || string.IsNullOrWhiteSpace(receipt.Signature.NameKey)
            || string.IsNullOrWhiteSpace(receipt.Signature.Kind)
            || string.IsNullOrWhiteSpace(receipt.Signature.Type))
        {
            throw new FormatException("digestion formalization receipt has an empty required field");
        }

        if (!Gid.TryParse(receipt.PrimaryGid, out var gid)
            || gid.ToTarget() is not Target.Formal { Declaration: not null })
        {
            throw new FormatException(
                $"digestion formalization primary_gid must select a Lean declaration: {receipt.PrimaryGid}");
        }

        if (!DigestionFingerprint.IsCanonicalSha256(receipt.CasRef)
            || !DigestionFingerprint.IsCanonicalSha256(receipt.RawSha256))
        {
            throw new FormatException(
                "digestion formalization receipt fingerprints must be canonical sha256:<64 lowercase hex>");
        }
    }

    private static void RequireFields(
        JsonElement element,
        ImmutableHashSet<string> expected,
        string label)
    {
        if (element.ValueKind != JsonValueKind.Object)
        {
            throw new FormatException($"{label} must be an object");
        }

        var actual = element.EnumerateObject().Select(static property => property.Name).ToArray();
        if (actual.Length != expected.Count
            || actual.Distinct(StringComparer.Ordinal).Count() != actual.Length
            || actual.Any(name => !expected.Contains(name)))
        {
            throw new FormatException($"{label} fields are not the closed schema");
        }
    }

    private static string RequireString(JsonElement element, string property)
    {
        var value = element.GetProperty(property);
        return value.ValueKind == JsonValueKind.String
            ? value.GetString()!
            : throw new FormatException($"{property} must be a string");
    }
}
