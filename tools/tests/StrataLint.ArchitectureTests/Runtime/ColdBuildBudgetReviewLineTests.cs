namespace StrataLint.ArchitectureTests;

public sealed class ColdBuildBudgetReviewLineTests
{
    [Fact]
    public void CommandCutoffAndConfiguredFloorRemainIndependentlyPinned()
    {
        Assert.Equal(21600, StrataLint.EngineeringScope.LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds);
        Assert.Equal(300, StrataLint.EngineeringScope.LeanCacheBudgetPolicy.MinimumConfigurableBudgetSeconds);
    }

    [Fact]
    public void DeclaredD5LeanFilesIncludeTheProtectedFrontier()
    {
        var d5Files = GitIndexRepositoryFiles.EnumerateDeclared(RepositoryLayout.FindRoot(), "D5");
        var leanFiles = d5Files
            .Where(static file => file.RelativePath.EndsWith(".lean", StringComparison.Ordinal))
            .ToArray();

        Assert.NotEmpty(d5Files);
        Assert.NotEmpty(leanFiles);
        Assert.Contains(leanFiles, static file => file.RelativePath == "D5/X_Frontier/Hearts.lean");
    }

    /// <summary>
    /// **`EnumerateDeclared` 自己的钉子** —— 它必须返回该前缀下的**每一个** tracked 文件。
    ///
    /// 这条是第四轮评审用实测买来的。此前 `ColdBuildBudgetReviewLineHasNotBeenCrossed`
    /// 想靠「与同一次枚举的上游集合做关系断言 + 一个 sentinel」自证枚举完整,
    /// 评审席实测证伪:子集断言 `leanFiles.Length &lt;= d5Files.Count` **由构造恒真**
    /// (`leanFiles` 就是从 `d5Files` 过滤来的),而单个 sentinel **可以被保留后任意截断** ——
    /// 它在 `EnumerateDeclared` 里加 `OrderByDescending(...).Take(n)` 并保留 `Hearts.lean`,
    /// 那一条与另外三条断言**全部照绿**,观察者从此永远看不到越线。
    ///
    /// **修法不是给消费者加更多断言,是给这个包装它自己的红。**
    /// 本测试独立跑一次全量 <see cref="GitIndexRepositoryFiles.Enumerate"/> 并自行过滤,
    /// 与 <see cref="GitIndexRepositoryFiles.EnumerateDeclared"/> 的结果**逐项比对**。
    ///
    /// **它到底证明了什么(第六轮评审逐句核过的表述)**:
    /// **在本次仓库快照上、限于 `D5` 前缀、以 `RelativePath` 为观察量时,
    /// 包装的输出序列与 Engine 输出经显式前缀过滤后的序列相等。**
    ///
    /// 此处原先写的是「任何截断、重排丢项或前缀语义漂移都会在这里红」,**那句比实际保证强**:
    /// * 若 Engine 层把**两边共同重排**,两个数组仍相等 —— 不红;
    /// * 若两个前缀谓词只在**当前数据里没有出现的路径形状**上语义不同,也仍全绿;
    /// * 其他前缀、以及 `RepositoryFile` 的**非 `RelativePath` 字段**完全未被覆盖。
    ///
    /// **保证边界(第五轮评审实测收窄,原文写错了)**:本测试**不证明**
    /// `StrataLint.Engine.GitIndexRepositoryFiles.Enumerate` 自身完整。
    ///
    /// 此处原本写的是「那是它的义务,由它众多的消费者共同承担(变异它会红一大片)」。
    /// **那句话被实测证伪**:评审席在 Engine 的 `File.Exists` 过滤后省略**一个**文件
    /// (`D5/S0/Asymptotics/Bonferroni/TailBounds.lean`),`exit=0`、232/232 全过、
    /// **红消费者 0 个**。只有**粗**截断(降序 `Take(32776)`)才会红 14 个,
    /// 而那 14 条守的是别的不变量,只是碰巧连带失败。
    ///
    /// 故准确的表述是:**Engine 的枚举在单文件粒度上无任何钉子**,已立 issue #3833。
    ///
    /// **但「本测试以 Engine 完整为前提」这句话是错的**(第六轮评审勘正):
    /// 本测试证的是一个**相对命题** —— 即使 Engine 同时漏掉一个文件,
    /// 只要包装没有再漏,两个序列**仍然相等,该相对命题仍为真**。
    /// **Engine 完整性只在把结论提升为「每一个 tracked 文件都在」这一绝对命题时才成为前提。**
    ///
    /// 同一句里的「仅此而已」则**比断言更弱**:`Assert.Equal` 是序列相等,
    /// 它同时排除了**包装独有的新增、重复计数变化与顺序变化**,不只是「没有再丢东西」。
    ///
    /// **若要主张绝对的 tracked-file 完整性**,除 Engine 完整外还依赖:
    /// 手写的 `StartsWith` 谓词代表正确的前缀语义、`RelativePath` 足以代表被比较的对象、
    /// 两次枚举观察的是同一稳定快照。这几条此前一条都没列出来。
    ///
    /// This test checks the wrapper against the Engine enumerator. Independent tracked-file
    /// completeness is a separate obligation recorded in #3833.
    /// </summary>
    [Fact]
    public void EnumerateDeclaredReturnsEveryTrackedFileUnderThePrefix()
    {
        var root = RepositoryLayout.FindRoot();

        var independent = GitIndexRepositoryFiles.Enumerate(root)
            .Where(static file => file.RelativePath.StartsWith("D5/", StringComparison.Ordinal))
            .Select(static file => file.RelativePath)
            .ToArray();
        var declared = GitIndexRepositoryFiles.EnumerateDeclared(root, "D5")
            .Select(static file => file.RelativePath)
            .ToArray();

        Assert.NotEmpty(independent);
        Assert.Equal(independent, declared);
    }
}
