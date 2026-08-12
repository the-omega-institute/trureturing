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

internal sealed record DigestionFormalizationExtension(
    string Gid,
    DigestionFormalizationSignature Signature);

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
    string RawSha256,
    ImmutableArray<DigestionFormalizationExtension> HostedExtensions = default)
{
    internal const string Schema = "digestion-formalization-v1";

    internal const string RootPath = "Meta/Digestion/formalizations/";

    internal const string PathSuffix = ".v1.json";

    internal static string PathFor(string atomId) => RootPath + atomId + PathSuffix;

    // Shape-only residence check for the closed-world path policy (SL-000): one
    // lowercase atom-id segment between the canonical root and the versioned
    // suffix. Content validity stays with Load; residence classification stays
    // with FILEMAP.
    internal static bool IsCanonicalPath(string path)
    {
        if (!path.StartsWith(RootPath, StringComparison.Ordinal)
            || !path.EndsWith(PathSuffix, StringComparison.Ordinal)
            || path.Length <= RootPath.Length + PathSuffix.Length)
        {
            return false;
        }

        foreach (var value in path.AsSpan(
            RootPath.Length,
            path.Length - RootPath.Length - PathSuffix.Length))
        {
            if (value is not ((>= 'a' and <= 'z') or (>= '0' and <= '9') or '-'))
            {
                return false;
            }
        }

        return true;
    }

    private static readonly ImmutableHashSet<string> RootFields = ImmutableHashSet.Create(
        StringComparer.Ordinal,
        "atom_id",
        "cas_ref",
        "precommitted_signature",
        "primary_gid",
        "raw_sha256",
        "schema");

    private static readonly ImmutableHashSet<string> ExtendedRootFields =
        RootFields.Add("hosted_extensions");

    private static readonly ImmutableHashSet<string> ExtensionFields = ImmutableHashSet.Create(
        StringComparer.Ordinal,
        "gid",
        "precommitted_signature");

    private static readonly ImmutableHashSet<string> SignatureFields = ImmutableHashSet.Create(
        StringComparer.Ordinal,
        "kind",
        "name_key",
        "type");

    internal static ImmutableArray<byte> Write(DigestionFormalizationReceipt receipt)
    {
        ArgumentNullException.ThrowIfNull(receipt);
        Validate(receipt);
        var hostedExtensions = Extensions(receipt);
        if (hostedExtensions.IsEmpty)
        {
            var material = new
            {
                atom_id = receipt.AtomId,
                cas_ref = receipt.CasRef,
                precommitted_signature = SignatureMaterial(receipt.Signature),
                primary_gid = receipt.PrimaryGid,
                raw_sha256 = receipt.RawSha256,
                schema = Schema,
            };
            return StructuredCanonicalWriter.WriteJson(JsonSerializer.SerializeToElement(material));
        }

        var extendedMaterial = new
        {
            atom_id = receipt.AtomId,
            cas_ref = receipt.CasRef,
            hosted_extensions = hostedExtensions.Select(extension => new
            {
                gid = extension.Gid,
                precommitted_signature = SignatureMaterial(extension.Signature),
            }).ToArray(),
            precommitted_signature = SignatureMaterial(receipt.Signature),
            primary_gid = receipt.PrimaryGid,
            raw_sha256 = receipt.RawSha256,
            schema = Schema,
        };
        return StructuredCanonicalWriter.WriteJson(JsonSerializer.SerializeToElement(extendedMaterial));
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

        var hasHostedExtensions = document.RootElement.TryGetProperty("hosted_extensions", out var extensionsElement);
        RequireFields(
            document.RootElement,
            hasHostedExtensions ? ExtendedRootFields : RootFields,
            "root");
        if (RequireString(document.RootElement, "schema") != Schema)
        {
            throw new FormatException($"schema must be {Schema}");
        }

        var signatureElement = document.RootElement.GetProperty("precommitted_signature");
        RequireFields(signatureElement, SignatureFields, "precommitted_signature");
        var hostedExtensions = ImmutableArray.CreateBuilder<DigestionFormalizationExtension>();
        if (hasHostedExtensions)
        {
            if (extensionsElement.ValueKind != JsonValueKind.Array
                || extensionsElement.GetArrayLength() == 0)
            {
                throw new FormatException("hosted_extensions must be a non-empty array");
            }

            foreach (var extensionElement in extensionsElement.EnumerateArray())
            {
                RequireFields(extensionElement, ExtensionFields, "hosted extension");
                var extensionSignature = extensionElement.GetProperty("precommitted_signature");
                RequireFields(
                    extensionSignature,
                    SignatureFields,
                    "hosted extension precommitted_signature");
                hostedExtensions.Add(new DigestionFormalizationExtension(
                    RequireString(extensionElement, "gid"),
                    ReadSignature(extensionSignature)));
            }
        }

        var receipt = new DigestionFormalizationReceipt(
            RequireString(document.RootElement, "atom_id"),
            RequireString(document.RootElement, "primary_gid"),
            ReadSignature(signatureElement),
            RequireString(document.RootElement, "cas_ref"),
            RequireString(document.RootElement, "raw_sha256"),
            hostedExtensions.ToImmutable());
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
            || string.IsNullOrWhiteSpace(receipt.PrimaryGid))
        {
            throw new FormatException("digestion formalization receipt has an empty required field");
        }

        ValidateSignature(receipt.Signature);

        if (!SelectsDeclaration(receipt.PrimaryGid))
        {
            throw new FormatException(
                $"digestion formalization primary_gid must select a Lean declaration: {receipt.PrimaryGid}");
        }

        var extensions = Extensions(receipt);
        if (extensions.Select(static extension => extension.Gid)
                .Distinct(StringComparer.Ordinal).Count() != extensions.Length)
        {
            throw new FormatException("digestion formalization hosted extension GIDs must be unique");
        }

        if (!extensions.SequenceEqual(extensions.OrderBy(static extension => extension.Gid, StringComparer.Ordinal)))
        {
            throw new FormatException("digestion formalization hosted extensions must be ordered by GID");
        }

        foreach (var extension in extensions)
        {
            if (string.Equals(extension.Gid, receipt.PrimaryGid, StringComparison.Ordinal)
                || !SelectsDeclaration(extension.Gid))
            {
                throw new FormatException(
                    $"digestion formalization hosted extension must select a secondary declaration: {extension.Gid}");
            }

            ValidateSignature(extension.Signature);
        }

        if (!DigestionFingerprint.IsCanonicalSha256(receipt.CasRef)
            || !DigestionFingerprint.IsCanonicalSha256(receipt.RawSha256))
        {
            throw new FormatException(
                "digestion formalization receipt fingerprints must be canonical sha256:<64 lowercase hex>");
        }
    }

    private static ImmutableArray<DigestionFormalizationExtension> Extensions(
        DigestionFormalizationReceipt receipt) =>
        receipt.HostedExtensions.IsDefault ? [] : receipt.HostedExtensions;

    private static object SignatureMaterial(DigestionFormalizationSignature signature) => new
    {
        kind = signature.Kind,
        name_key = signature.NameKey,
        type = signature.Type,
    };

    private static DigestionFormalizationSignature ReadSignature(JsonElement element) => new(
        RequireString(element, "name_key"),
        RequireString(element, "kind"),
        RequireString(element, "type"));

    private static void ValidateSignature(DigestionFormalizationSignature signature)
    {
        if (string.IsNullOrWhiteSpace(signature.NameKey)
            || string.IsNullOrWhiteSpace(signature.Kind)
            || string.IsNullOrWhiteSpace(signature.Type))
        {
            throw new FormatException("digestion formalization receipt has an empty required field");
        }
    }

    private static bool SelectsDeclaration(string gidText) =>
        Gid.TryParse(gidText, out var gid)
        && gid.ToTarget() is Target.Formal { Declaration: not null };

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

internal static class DigestionFormalizationReceiptVerifier
{
    internal static void RequireAuthorizedCoverage(
        RepositorySnapshot authority,
        string receiptPath,
        DigestionLedgerEntry atom,
        IEnumerable<string> priorCoverage,
        IEnumerable<string> addedCoverage,
        LeanAxiomReport report)
    {
        ArgumentNullException.ThrowIfNull(authority);
        ArgumentException.ThrowIfNullOrWhiteSpace(receiptPath);
        ArgumentNullException.ThrowIfNull(atom);
        ArgumentNullException.ThrowIfNull(priorCoverage);
        ArgumentNullException.ThrowIfNull(addedCoverage);
        ArgumentNullException.ThrowIfNull(report);

        var canonicalPath = DigestionFormalizationReceipt.PathFor(atom.AtomId);
        if (!string.Equals(receiptPath, canonicalPath, StringComparison.Ordinal))
        {
            throw new FormatException(
                $"base-owned formalization receipt for atom {atom.AtomId} must use {canonicalPath}");
        }

        DigestionFormalizationReceipt receipt;
        try
        {
            receipt = DigestionFormalizationReceipt.Load(authority, receiptPath);
        }
        catch (Exception exception) when (exception is FormatException or JsonException)
        {
            throw new FormatException(
                $"base-owned formalization receipt for atom {atom.AtomId} is invalid: {exception.Message}",
                exception);
        }

        if (!string.Equals(receipt.AtomId, atom.AtomId, StringComparison.Ordinal))
        {
            throw new FormatException(
                $"base-owned formalization receipt atom_id {receipt.AtomId} "
                + $"does not match atom {atom.AtomId}");
        }

        if (!string.Equals(receipt.CasRef, atom.CasRef, StringComparison.Ordinal)
            || !string.Equals(receipt.RawSha256, atom.Fingerprints.RawSha256, StringComparison.Ordinal))
        {
            throw new FormatException(
                $"base-owned formalization receipt fingerprint does not match atom {atom.AtomId}");
        }

        var prior = priorCoverage.ToImmutableHashSet(StringComparer.Ordinal);
        var added = addedCoverage.Distinct(StringComparer.Ordinal).ToArray();
        if (atom.CoverageGids.Length > 0
            && !atom.CoverageGids.Contains(receipt.PrimaryGid, StringComparer.Ordinal))
        {
            throw new FormatException(
                $"base-owned formalization receipt primary_gid {receipt.PrimaryGid} "
                + $"is absent from current coverage for atom {atom.AtomId}");
        }

        if (prior.Count == 0 && !added.Contains(receipt.PrimaryGid, StringComparer.Ordinal))
        {
            throw new FormatException(
                $"base-owned formalization receipt primary_gid {receipt.PrimaryGid} "
                + "does not match --gid values");
        }

        if (prior.Count > 0 && !prior.Contains(receipt.PrimaryGid))
        {
            throw new FormatException(
                $"base-owned formalization receipt primary_gid {receipt.PrimaryGid} "
                + $"does not match existing coverage for atom {atom.AtomId}");
        }

        var signaturesToCheck = receipt.HostedExtensions
            .Select(static extension => extension.Gid)
            .Concat(added)
            .Append(receipt.PrimaryGid)
            .Distinct(StringComparer.Ordinal);
        foreach (var gidText in signaturesToCheck)
        {
            var pinned = string.Equals(gidText, receipt.PrimaryGid, StringComparison.Ordinal)
                ? receipt.Signature
                : receipt.HostedExtensions
                    .Where(extension => string.Equals(extension.Gid, gidText, StringComparison.Ordinal))
                    .Select(static extension => extension.Signature)
                    .SingleOrDefault()
                    ?? throw new FormatException(
                        $"coverage GID {gidText} has no base-owned pre-committed signature");
            if (!Gid.TryParse(gidText, out var gid))
            {
                throw new FormatException($"formalization coverage GID is invalid: {gidText}");
            }

            var current = DigestionFormalizationReceipt.ResolveSignature(gid, report);
            if (current != pinned)
            {
                throw new FormatException(
                    $"declaration {gidText} signature "
                    + $"({current.NameKey}, {current.Kind}, {current.Type}) "
                    + "does not match the pre-committed signature (base-owned) "
                    + $"({pinned.NameKey}, {pinned.Kind}, {pinned.Type})");
            }
        }
    }
}
