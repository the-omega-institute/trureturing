using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.Cli;

internal static partial class FileMapPolicy
{
    // The declaration package is admitted before its first source module.
    // Only its three lawful content families reserve an empty source set.
    private static bool IsRegFamilyReservation(
        FileMapEntry entry, FileMapManifest manifest, IReadOnlySet<string> trackedPaths) =>
        entry.Pattern is "Reg/D5/**/*.lean" or "Reg/Support/**/*.lean" or "Reg/Catalogs/**/*.lean"
        && entry.Kind is FileMapKind.Data && entry.AdmissionPlane is FileMapAdmissionPlane.Content
        && entry.VerifiedBy.Contains("lean-build") && entry.VerifiedBy.Contains("lean-inspector")
        && HasPackageConfig(RegManifestAgreement.LakefilePath, manifest, trackedPaths)
        && HasPackageConfig(RegManifestAgreement.ManifestPath, manifest, trackedPaths);

    private static bool HasPackageConfig(
        string path, FileMapManifest manifest, IReadOnlySet<string> trackedPaths) =>
        trackedPaths.Contains(path)
        && manifest.Match(path) is [{ Kind: FileMapKind.Program, AdmissionPlane: FileMapAdmissionPlane.Judge }];
}
