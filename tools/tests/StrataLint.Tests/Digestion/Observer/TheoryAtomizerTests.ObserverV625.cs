using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class TheoryAtomizerTests
{
    [Theory]
    [InlineData("**§37.1 率的世界**。claim。")]
    [InlineData("**§37.2 尺子的性格表**。claim。")]
    [InlineData("**§38.1 塔的全貌**。claim。")]
    [InlineData("**§38.2 周期之句点**。claim。")]
    [InlineData("**§39.1 最后的地图**。claim。")]
    [InlineData("**§39.2 匿名的教益**。claim。")]
    [InlineData("**§40.1 算术的住址**。claim。")]
    [InlineData("**§40.2 水位线与门**。claim。")]
    [InlineData("**§41.1 词典与墙**。claim。")]
    [InlineData("**§41.2 山腰的账**。claim。")]
    [InlineData("**§42.1 四律**。claim。")]
    [InlineData("**§42.2 刀锋之外**。claim。")]
    [InlineData("**§43.1 问与答的形状**。claim。")]
    [InlineData("**§43.2 语法与门后**。claim。")]
    [InlineData("**§44.1 价目与王冠**。claim。")]
    [InlineData("**§44.2 三层与塔顶**。claim。")]
    [InlineData("**§45.1 蒙难记与星座**。claim。")]
    [InlineData("**§45.2 合卷**。claim。")]
    [InlineData("**§46.1 界面**。claim。")]
    [InlineData("**§46.2 合卷**。claim。")]
    [InlineData("**§47.1 会自我审稿的论文,会自我复制的塔**。claim。")]
    [InlineData("**§47.2 搁笔**。claim。")]
    public void ObserverV1RecognizesSections37Through47(string claim)
    {
        var bytes = Encoding.UTF8.GetBytes($"# Observer\n\n{claim}\n");

        var atom = Assert.Single(AtomizerRegistry.Atomize(
            AtomizerRegistry.ObserverId,
            bytes,
            DigestionTestSupport.Rules).Claims);

        AssertContentIdentity(atom);
    }
}
