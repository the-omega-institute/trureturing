using System.Security.Cryptography;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class TheoryAtomizerTests
{
    [Theory]
    [InlineData("**§37.1 率的世界**。claim。", "metric-rates/rate-world")]
    [InlineData("**§37.2 尺子的性格表**。claim。", "metric-rates/metric-character")]
    [InlineData("**§38.1 塔的全貌**。claim。", "research-boundary/tower-overview")]
    [InlineData("**§38.2 周期之句点**。claim。", "research-boundary/cycle-closure")]
    [InlineData("**§39.1 最后的地图**。claim。", "nameability/final-map")]
    [InlineData("**§39.2 匿名的教益**。claim。", "nameability/anonymous-lesson")]
    [InlineData("**§40.1 算术的住址**。claim。", "stationary-points/arithmetic-address")]
    [InlineData("**§40.2 水位线与门**。claim。", "stationary-points/waterline-gates")]
    [InlineData("**§41.1 词典与墙**。claim。", "mountainside/dictionary-wall")]
    [InlineData("**§41.2 山腰的账**。claim。", "mountainside/ledger")]
    [InlineData("**§42.1 四律**。claim。", "diagonal-ledger/four-laws")]
    [InlineData("**§42.2 刀锋之外**。claim。", "diagonal-ledger/beyond-blade")]
    [InlineData("**§43.1 问与答的形状**。claim。", "six-questions/shape")]
    [InlineData("**§43.2 语法与门后**。claim。", "six-questions/grammar")]
    [InlineData("**§44.1 价目与王冠**。claim。", "tower-top/prices-crowns")]
    [InlineData("**§44.2 三层与塔顶**。claim。", "tower-top/three-layers")]
    [InlineData("**§45.1 蒙难记与星座**。claim。", "final-volume/trials-constellation")]
    [InlineData("**§45.2 合卷**。claim。", "final-volume/closure")]
    [InlineData("**§46.1 界面**。claim。", "interface/interface")]
    [InlineData("**§46.2 合卷**。claim。", "interface/closure")]
    public void ObserverV1RecognizesSections37Through46(
        string claim,
        string expectedAstPath)
    {
        var bytes = Encoding.UTF8.GetBytes($"# Observer\n\n{claim}\n");

        var atom = Assert.Single(AtomizerRegistry.Atomize(AtomizerRegistry.ObserverId, bytes).Claims);

        Assert.Equal(expectedAstPath, atom.AstPath);
    }

    [Fact]
    public void ObserverV1PreservesTheLegacyProductionAtomizationByteForByte()
    {
        var root = FindRepositoryRoot();
        var source = File.ReadAllBytes(Path.Combine(root, ThirdProductionSource));
        var document = AtomizerRegistry.Atomize(AtomizerRegistry.ObserverId, source);

        using var output = new MemoryStream();
        using (var writer = new BinaryWriter(output, Encoding.UTF8, leaveOpen: true))
        {
            foreach (var atom in document.Claims)
            {
                writer.Write(atom.AstPath);
                writer.Write(atom.StartByte);
                writer.Write(atom.EndByte);
                writer.Write(atom.RawBytes.Length);
                writer.Write(atom.RawBytes.AsSpan());
            }
        }

        Assert.Equal(
            "ffd91501b2e8bd7028272b9f423f6f85bcbcd7e214f0135fa5fde42df93bcb6f",
            Convert.ToHexString(SHA256.HashData(output.ToArray())).ToLowerInvariant());
    }
}
