using System.Text.Json;

namespace StrataLint.Scribe;

internal static class DescribeReportWriter
{
    private static readonly JsonSerializerOptions JsonOptions = new()
    {
        WriteIndented = true,
    };

    internal static string WriteJson(DescribeReport report)
    {
        ArgumentNullException.ThrowIfNull(report);
        var material = new
        {
            schema = "scribe-describe-report-v2",
            case_id = DescribeReport.CaseId,
            status = report.Status,
            projection_open_count = report.ProjectionOpenCount,
            node_stats = new
            {
                total = report.NodeStats.Total,
                formula_content_slots = report.NodeStats.FormulaContentSlots,
                formula_statements = report.NodeStats.FormulaStatements,
                lean_statements = report.NodeStats.LeanStatements,
                by_kind = report.NodeStats.ByKind,
                by_provenance = report.NodeStats.ByProvenance,
            },
            suspected_novel = report.SuspectedNovel.Select(Node),
            unprojectable = report.Unprojectable.Select(Node),
            nodes = report.Nodes.Select(Node),
            red_findings = report.RedFindings.Select(static finding => new
            {
                code = finding.Code,
                path = finding.Path,
                message = finding.Message,
            }),
            observations = report.Observations.Select(static observation => new
            {
                code = observation.Code,
                path = observation.Path,
                detail = observation.Detail,
            }),
        };
        return JsonSerializer.Serialize(material, JsonOptions) + "\n";
    }

    internal static string WriteText(DescribeReport report)
    {
        ArgumentNullException.ThrowIfNull(report);
        var writer = new StringWriter(System.Globalization.CultureInfo.InvariantCulture);
        writer.WriteLine(
            $"DESCRIBE_STATUS case={DescribeReport.CaseId} status={report.Status} "
            + $"nodes={report.NodeStats.Total} "
            + $"suspected_novel={report.SuspectedNovel.Length} "
            + $"formula_content_slots={report.NodeStats.FormulaContentSlots} "
            + $"formula_statements={report.NodeStats.FormulaStatements} "
            + $"red={report.RedFindings.Length} observe={report.Observations.Length}");
        foreach (var node in report.SuspectedNovel)
        {
            writer.WriteLine($"SUSPECTED_NOVEL node={node.NodeId} title={JsonSerializer.Serialize(node.Title)}");
        }
        foreach (var node in report.Unprojectable)
        {
            writer.WriteLine($"OPEN projection node={node.NodeId} reason={node.ProjectionFailureReason}");
        }
        foreach (var node in report.Nodes.Where(static node => node.OpenProblemResolutionClaim is not null))
        {
            var claim = node.OpenProblemResolutionClaim!;
            writer.WriteLine(
                $"OPEN_PROBLEM_RESOLUTION node={node.NodeId} problem_slug={claim.ProblemSlug.Value} "
                + $"resolution_kind={DescribeVocabulary.CanonicalName(claim.ResolutionKind)}");
        }
        foreach (var finding in report.RedFindings)
        {
            writer.WriteLine(
                $"RED code={finding.Code} path={finding.Path} message={JsonSerializer.Serialize(finding.Message)}");
        }
        foreach (var observation in report.Observations)
        {
            writer.WriteLine(
                $"OBSERVE code={observation.Code} path={observation.Path} detail={JsonSerializer.Serialize(observation.Detail)}");
        }

        return writer.ToString();
    }

    private static object Node(DescribeNodeRecord node) => new
    {
        node_id = node.NodeId,
        document_gid = node.DocumentGid,
        kind = node.Kind,
        title = node.Title,
        statement_kind = node.StatementKind,
        formula_provenance = node.FormulaProvenance,
        projection_failure_reason = node.ProjectionFailureReason,
        provenance = node.Provenance,
        literature_gid = node.LiteratureGid,
        acknowledgement_gids = node.AcknowledgementGids,
        open_problem_resolution = node.OpenProblemResolutionClaim is not { } claim
            ? null
            : new
            {
                problem_slug = claim.ProblemSlug.Value,
                resolution_kind = DescribeVocabulary.CanonicalName(claim.ResolutionKind),
            },
    };
}
