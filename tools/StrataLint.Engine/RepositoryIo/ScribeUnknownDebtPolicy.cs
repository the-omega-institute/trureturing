using System.Collections.Immutable;

namespace StrataLint.Engine;

internal sealed record ScribeUnknownDebtPartitionV1(
    string Key,
    ImmutableSortedDictionary<string, ScribeTestMethod> UnknownMethods);

internal sealed record ScribeUnknownDebtBaselineV1(
    int SchemaVersion,
    ImmutableSortedDictionary<string, ScribeUnknownDebtPartitionV1> Partitions)
{
    internal const int CurrentSchemaVersion = 1;

    internal int UnknownCount => Partitions.Values.Sum(static partition => partition.UnknownMethods.Count);

    internal static ScribeUnknownDebtBaselineV1 Create(ScribeTestMap map)
    {
        var partitions = map.Methods
            .Where(static method => method.IsUnknown)
            .GroupBy(static method => method.PartitionKey, StringComparer.Ordinal)
            .ToImmutableSortedDictionary(
                static group => group.Key,
                static group => new ScribeUnknownDebtPartitionV1(
                    group.Key,
                    group.GroupBy(static method => method.Identity, StringComparer.Ordinal)
                        .ToImmutableSortedDictionary(
                            static methods => methods.Key,
                            static methods => methods.Single(),
                            StringComparer.Ordinal)),
                StringComparer.Ordinal);
        return new ScribeUnknownDebtBaselineV1(CurrentSchemaVersion, partitions);
    }

    internal IEnumerable<ScribeTestMethod> UnknownMethods() =>
        Partitions.Values.SelectMany(static partition => partition.UnknownMethods.Values);

    internal bool Contains(ScribeTestMethod method) => UnknownMethods().Any(candidate =>
        new[]
        {
            candidate.PartitionKey == method.PartitionKey,
            candidate.SourcePath == method.SourcePath,
            candidate.Id == method.Id,
        }.All(static componentMatches => componentMatches));
}

internal sealed record ScribeUnknownDebtFinding(
    string Path,
    string Message,
    AdmissionEffect Effect);

internal static class ScribeUnknownDebtPolicy
{
    // The admission debt line remains the phase-4a value. New unknown identities block even
    // below this line; the number describes inherited debt, not spendable capacity.
    internal const int UnknownDebtLimit = 280;

    // policy-override #2204, 2026-08-17. Domain: repository-read test methods that the
    // conservative parser cannot resolve. Positive reading: both merge parents had 280 and
    // their union had 281. Negative boundary: 282 was not observed and remains a repository-wide
    // block. Owner: repository tau=0 owner. Exit: remove this reserve after every branch forked
    // before the v1 partitioned-delta rule landed is merged or closed and dev is back at <= 280.
    internal const int ConcurrentMergeReserve = 1;

    internal const int UnknownDebtToleranceLimit = UnknownDebtLimit + ConcurrentMergeReserve;

    internal static ImmutableArray<ScribeUnknownDebtFinding> Evaluate(
        ScribeTestMap currentMap,
        ScribeTestMap forkPointMap)
    {
        var current = ScribeUnknownDebtBaselineV1.Create(currentMap);
        var forkPoint = ScribeUnknownDebtBaselineV1.Create(forkPointMap);
        var forkPointIdentities = forkPointMap.Methods
            .Select(static method => (method.PartitionKey, method.SourcePath, method.Id))
            .ToHashSet();
        var findings = ImmutableArray.CreateBuilder<ScribeUnknownDebtFinding>();
        AddManagedTestLayoutFindings(currentMap, findings);
        // 身份含 SourcePath 与 PartitionKey,故**把一个 unknown 方法搬到别处**会被判为新增,
        // 尽管搬迁既不增也不减 parser 债。本战线的核心动作就是在项目之间搬测试(#5419),
        // 于是该判据把「还债」本身挡住了。抵扣按下述配对进行,不是放宽:
        //   ① 只有**离开**候选树的 base unknown 才进入抵扣池(仅仅由 unknown 变 known 的不算 ——
        //      那是真实减债,不该被拿去买一条新债);
        //   ② 抵扣要求 `Id`(即 `类型名.方法名`)与 unknown 成因集合**都相同** ——
        //      同名而成因不同不是同一笔债;
        //   ③ 抵扣是**配对**不是谓词:每个离开者只能豁免一个新增,删一条不能买两条。
        var currentIdentities = currentMap.Methods
            .Select(static method => (method.PartitionKey, method.SourcePath, method.Id))
            .ToHashSet();
        var vacated = new Dictionary<string, int>(StringComparer.Ordinal);
        foreach (var method in forkPoint.UnknownMethods().Where(method =>
                     !currentIdentities.Contains(
                         (method.PartitionKey, method.SourcePath, method.Id))))
        {
            var key = RelocationKey(method);
            vacated[key] = vacated.GetValueOrDefault(key) + 1;
        }

        var introducedBuilder = ImmutableArray.CreateBuilder<ScribeTestMethod>();
        foreach (var method in current.UnknownMethods()
                     .Where(method => !forkPointIdentities.Contains(
                         (method.PartitionKey, method.SourcePath, method.Id)))
                     .OrderBy(static method => method.PartitionKey, StringComparer.Ordinal)
                     .ThenBy(static method => method.SourcePath, StringComparer.Ordinal)
                     .ThenBy(static method => method.Id, StringComparer.Ordinal))
        {
            var key = RelocationKey(method);
            if (vacated.TryGetValue(key, out var remaining) && remaining > 0)
            {
                vacated[key] = remaining - 1;
                continue;
            }

            introducedBuilder.Add(method);
        }

        var introduced = introducedBuilder.ToArray();

        if (current.UnknownCount > UnknownDebtToleranceLimit)
        {
            findings.Add(new ScribeUnknownDebtFinding(
                "tools/tests",
                $"repository contains {current.UnknownCount} conservative unknown test methods "
                    + $"(admission limit {UnknownDebtLimit}, repository tolerance "
                    + $"{UnknownDebtToleranceLimit}; reduce parser debt)",
                AdmissionEffect.Block));
        }
        else if (current.UnknownCount > UnknownDebtLimit && introduced.Length == 0)
        {
            findings.Add(new ScribeUnknownDebtFinding(
                "tools/tests",
                $"repository contains {current.UnknownCount} conservative unknown test methods "
                    + $"(admission limit {UnknownDebtLimit}, repository tolerance "
                    + $"{UnknownDebtToleranceLimit}), but this change introduced none",
                AdmissionEffect.Observe));
        }

        foreach (var method in introduced)
        {
            findings.Add(new ScribeUnknownDebtFinding(
                method.SourcePath,
                $"conservative unknown test method introduced after fork point: "
                    + method.DisplayIdentity,
                AdmissionEffect.Block));
        }

        return findings.ToImmutable();
    }

    internal static ImmutableArray<ScribeUnknownDebtFinding> InspectCurrent(ScribeTestMap currentMap)
    {
        var current = ScribeUnknownDebtBaselineV1.Create(currentMap);
        var findings = ImmutableArray.CreateBuilder<ScribeUnknownDebtFinding>();
        AddManagedTestLayoutFindings(currentMap, findings);
        if (current.UnknownCount > UnknownDebtToleranceLimit)
        {
            findings.Add(new ScribeUnknownDebtFinding(
                "tools/tests",
                $"repository contains {current.UnknownCount} conservative unknown test methods "
                    + $"(admission limit {UnknownDebtLimit}, repository tolerance "
                    + $"{UnknownDebtToleranceLimit}; reduce parser debt)",
                AdmissionEffect.Block));
        }

        return findings.ToImmutable();
    }

    // 抵扣键刻意**不含** PartitionKey 与 SourcePath —— 那正是搬迁会变、而债不变的两项。
    // UnknownReasons 在 ScribeTestMapDeriver 构造时已排序,故此处直接连接即可。
    private static string RelocationKey(ScribeTestMethod method) =>
        method.Id + "\u0000" + string.Join(",", method.UnknownReasons);

    private static void AddManagedTestLayoutFindings(
        ScribeTestMap map,
        ImmutableArray<ScribeUnknownDebtFinding>.Builder findings)
    {
        foreach (var finding in map.CompileQueryFindings)
        {
            findings.Add(new ScribeUnknownDebtFinding(
                finding.Path,
                finding.Message,
                AdmissionEffect.Block));
        }

        foreach (var path in map.UnclassifiedManagedProjectPaths)
        {
            findings.Add(new ScribeUnknownDebtFinding(
                path,
                "managed test project is neither an xUnit project with a direct PackageReference "
                    + "nor a declared compile-fail proof exemption",
                AdmissionEffect.Block));
        }

        foreach (var path in map.OrphanManagedSourcePaths)
        {
            findings.Add(new ScribeUnknownDebtFinding(
                path,
                "managed source is absent from every tracked project's MSBuild Compile items",
                AdmissionEffect.Block));
        }

        foreach (var path in map.DanglingCompileFailProofProjectExemptionPaths)
        {
            findings.Add(new ScribeUnknownDebtFinding(
                path,
                "declared compile-fail proof exemption does not name an existing tracked project",
                AdmissionEffect.Block));
        }
    }
}
