using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233178RecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Recurrence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The all-width recurrence for the literal normalized six-colour five-row array count.",
        H("From exact source cardinalities to the full recurrence"), Blocks(
            Paragraph(Text("The source count and FullE are those of HardinA233178Literal. "
                + "The transfer uses the original five rows as five independent base-three digits. "
                + "Its three-label columns are an auxiliary representation of the source graph. "
                + "No continuation or source-correspondence hypothesis is assumed.")),
            Node("count_transfer", "Exact column cardinality bridge", "For every natural n, "
                + "chromaticCount(n+1) is the sum of the continuation vector v(n). The explicit "
                + "base-three equivalence is a bijection between all 243 columns and all functions "
                + "from the five rows into three labels. Applying it columnwise is a bijection "
                + "with the actual array function domain. Literal edges become exactly Bond. "
                + "The original generic cont_matrix theorem counts all continuations; its "
                + "pair condition is True, its triple condition tests the last two columns, "
                + "and its class is the last column. No initial-column multiplicity is lost.", DescribeRole.Theorem),
            Node("chromatic_recurrence", "All subsequent chromatic widths", "For every natural n, "
                + "write C(k)=chromaticCount(k). Then "
                + "C(n+12)=6*C(n+11)+31*C(n+10)-97*C(n+9)-163*C(n+8) "
                + "+417*C(n+7)+93*C(n+6)-514*C(n+5)+192*C(n+4)+72*C(n+3)-36*C(n+2). "
                + "The exact source cardinality bridge and the certified vector identity give this relation. "
                + "The finite vector certificate propagates by arbitrary further matrix powers.", DescribeRole.Theorem),
            Node("result", "The literal FullE theorem", "The theorem proves FullE itself. "
                + "The chromatic coefficients sum to one, so adding six preserves the unscaled "
                + "recurrence. Substitution of 48*a(n)=32^n*(chromaticCount(n)+6) multiplies "
                + "the coefficient at lag i by 32^i. All lag widths are at least two when the "
                + "source width exceeds eleven. Integer cancellation then gives exactly the "
                + "ten coefficients in FullE. The theorem has no source-bridge assumption, "
                + "finite upper cutoff, changed onset, generating-function condition, "
                + "minimal-order assertion or colour-surjectivity hypothesis.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin233178"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, resolution);
}
