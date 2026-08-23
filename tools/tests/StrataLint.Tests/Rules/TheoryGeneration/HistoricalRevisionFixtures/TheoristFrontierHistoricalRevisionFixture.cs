namespace StrataLint.Tests;

internal sealed record HistoricalFrontierRevisionScene(
    int Scene,
    string BaselineSource,
    string BaselineBlobOid,
    string CandidateSource,
    string CandidateBlobOid,
    string StatementSha256);

internal static partial class TheoristFrontierHistoricalRevisionFixture
{
    private const string StatementSha =
        "sha256:25ddd0972fd7b97c88f87ea47bb9843e5c014cdad5344c37451293f18cb4a0d9";

    internal static HistoricalFrontierRevisionScene Get(int scene) => scene switch
    {
        // Provenance only: scene 9, baseline 54fe11737c9d83a0794121b66c41a3c01b25f1be, candidate e5dc4e2eb0ad90dead00dcaaa18871653857abe9.
        9 => Create(9, Blob7c7a8509, "7c7a8509e8a07b330795341f125ed99078d0afd7", Blob379c55a6, "379c55a672797dd8210c00f5d13e7caf072dcd04"),
        // Provenance only: scene 10, baseline e5dc4e2eb0ad90dead00dcaaa18871653857abe9, candidate 8b82f2c4f15336438711376dd1f35864c52ecfae.
        10 => Create(10, Blob379c55a6, "379c55a672797dd8210c00f5d13e7caf072dcd04", BlobC868750e, "c868750e57b77c27c1728eeb572671e19a194936"),
        // Provenance only: scene 11, baseline 8b82f2c4f15336438711376dd1f35864c52ecfae, candidate da1cc8656013946dbace193eb6469190fb66e664.
        11 => Create(11, BlobC868750e, "c868750e57b77c27c1728eeb572671e19a194936", Blob7967fb65, "7967fb65511ca6c35304b0a452035ba1a6af3afc"),
        // Provenance only: scene 12, baseline da1cc8656013946dbace193eb6469190fb66e664, candidate 56cb98317af755c099b40c983a15f98b53b9095a.
        12 => Create(12, Blob7967fb65, "7967fb65511ca6c35304b0a452035ba1a6af3afc", BlobD8047bf6, "d8047bf63b6451acfeab713787c27da88b51d2aa"),
        // Provenance only: scene 13, baseline 56cb98317af755c099b40c983a15f98b53b9095a, candidate 17375d3b099ce76ce6b7faad760d131ee987cdf2.
        13 => Create(13, BlobD8047bf6, "d8047bf63b6451acfeab713787c27da88b51d2aa", BlobDe84b99f, "de84b99fe75184145afa1e537cba253de7100777"),
        // Provenance only: scene 14, baseline 17375d3b099ce76ce6b7faad760d131ee987cdf2, candidate 3562a9aa8de78ae4b54d52674666bd2bd77d5e59.
        14 => Create(14, BlobDe84b99f, "de84b99fe75184145afa1e537cba253de7100777", BlobB2b7e0d7, "b2b7e0d77e80fc603d0eaaa77c66fc383dd8ce79"),
        // Provenance only: scene 16, baseline 84162846de144032a5f4bd3637e757cdc2378ca0, candidate b4a185b82388a060c3bc9d9e8e64ece3ad1e32f1.
        16 => Create(16, BlobB2b7e0d7, "b2b7e0d77e80fc603d0eaaa77c66fc383dd8ce79", BlobD44ceefa, "d44ceefa8219b743f9018aa3d9335cde956e5cee"),
        // Provenance only: scene 17, baseline b4a185b82388a060c3bc9d9e8e64ece3ad1e32f1, candidate f86dd2ba372fca7d90047caf6d35ac11cadcca5f.
        17 => Create(17, BlobD44ceefa, "d44ceefa8219b743f9018aa3d9335cde956e5cee", BlobCc57e467, "cc57e467892a7705d26959d3941756c621f81b58"),
        _ => throw new ArgumentOutOfRangeException(nameof(scene), scene, "Unknown historical scene."),
    };

    private static HistoricalFrontierRevisionScene Create(
        int scene,
        string baselineSource,
        string baselineBlobOid,
        string candidateSource,
        string candidateBlobOid) => new(
            scene,
            baselineSource + "\n",
            "git-sha1:" + baselineBlobOid,
            candidateSource + "\n",
            "git-sha1:" + candidateBlobOid,
            StatementSha);
}
