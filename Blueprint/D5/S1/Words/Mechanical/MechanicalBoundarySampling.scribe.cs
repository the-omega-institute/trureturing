using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical;

internal sealed class MechanicalBoundarySamplingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Derive exact arbitrary-schedule residuals from the proved two-site mechanical boundary law.",
        H("Targeted Sampling of Mechanical Boundary Pairs"),
        Blocks(
            Paragraph(Text(
                "For a fixed irrational slope strictly between zero and one, compare the actual "
                + "lower and upper traces at the same boundary index m. A set A of sample times "
                + "detects m precisely when it contains m-1 or m. Write D(A) for these detected "
                + "indices. The carrier being analyzed is this paired boundary family, not all "
                + "pairs of distinct rotation phases.")),
            Describe.Lean(
                DescribeId.Create("mechanical-arbitrary-schedule-residual"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Mechanical/MechanicalBoundarySampling.residual_eq"),
                H("The target-relevant residual is an exact set difference"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("Residual"), Open, F.Id("A"), Comma, F.Id("B"), Close,
                    Sp, Eq, Sp, F.Id("D"), Open, F.Id("B"), Close,
                    Sp, Minus, Sp, F.Id("D"), Open, F.Id("A"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Here minus denotes set difference. Agreement on A means m is outside D(A), "
                    + "and disagreement on the target B means m is inside D(B). These facts use "
                    + "the actual floor/ceiling disagreement theorem, so the set formula is "
                    + "not postulated as an observer interface."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mechanical-sampling-recovery-criterion"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Mechanical/MechanicalBoundarySampling.pair_target_recovery_iff"),
                H("Target recovery depends on sample locations, not only their number"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("Residual"), Open, F.Id("A"), Comma, F.Id("B"), Close,
                    Sp, Eq, Sp, OpenBrace, CloseBrace))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "All paired boundary sides that agree on A agree on B exactly when D(B) "
                    + "is a subset of D(A), equivalently when the displayed residual is empty. "
                    + "The theorem allows infinite or irregular schedules. Adding C removes "
                    + "exactly the former residual indices in D(C). It does not claim that "
                    + "resolving these pairs proves recovery of every possible hidden phase."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mechanical-past-interval-residual"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Mechanical/MechanicalBoundarySampling.past_to_segment_residual"),
                H("A complete scalar past leaves exactly the uncovered interval"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("Residual"), Sp, Eq, Sp, OpenBrace,
                    F.Id("m"), Sp, Colon, Sp, F.Id("J"), Sp, Lt, Sp,
                    F.Id("m"), Sp, Leq, Sp, F.Id("M"), CloseBrace))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For natural J and M, observing all integer sample times t<J and targeting "
                    + "times 0 through M-1 leaves precisely J<m<=M. This is an exact equality "
                    + "of the indexed pair-residual sets, including empty target intervals."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mechanical-boundary-probe-bound"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Mechanical/MechanicalBoundarySampling.boundary_probe_lower_bound"),
                H("One point sample resolves at most two boundary-pair indices"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("card"), Open, F.Id("R"), Close, Sp, Leq, Sp,
                    D(2), Sp, F.Id("card"), Open, F.Id("S"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If a finite sample set S distinguishes every pair in a specified finite "
                    + "boundary-index family R, then R lies in S union (S+1), whose cardinality "
                    + "is at most twice that of S. Consequently at least ceiling(card(R)/2) "
                    + "point samples are necessary. This lower bound is not asserted to be a "
                    + "complete minimal observer construction over all phases."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mechanical-boundary-cover-not-global"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Mechanical/MechanicalBoundarySampling.boundary_cover_not_full_recovery"),
                H("Covering boundary pairs does not recover arbitrary states"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("GlobalRecoveryFromEndpoints"), Sp, Rightarrow, Sp, F.Id("False")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every slope strictly between one quarter and one third, the actual "
                    + "lower traces at boundaries 0 and -2 begin 000 and 010. Samples at 0 "
                    + "and 2 agree while the middle target differs. Nevertheless D({1}) is "
                    + "contained in D({0,2}). This explicit family refutes promotion of the "
                    + "paired-boundary criterion to a full-state sufficiency theorem. Equal "
                    + "sample labels can occur on disconnected phase components."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Words/Mechanical/MechanicalPastSeparation")),
        ]));
}
