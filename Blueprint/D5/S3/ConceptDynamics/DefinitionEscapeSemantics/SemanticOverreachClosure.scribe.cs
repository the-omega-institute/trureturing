using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeSemantics;

internal sealed class SemanticOverreachClosureDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/DefinitionEscapeSemantics/"
            + "SemanticOverreachClosure.semantic_overreach_iff_not_overreach_closure";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Semantic overreach is exactly the absence of a licensed closing report.",
        H("Semantic Overreach Closure"),
        Blocks(Describe.Lean(
            DescribeId.Create("semantic-overreach-closure"),
            DeclarationHandle.Create(Declaration),
            H("Strict expansion overreaches exactly when no report license closes it"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A licensed semantic transport report carries a typed certificate for "
                        + "the same claim, source domain, reported domain, and claim version, "
                        + "and preserves the certificate premises exactly as its condition.")),
                Paragraph(Text(
                    "Given the directed strict expansion and the exact original claim scope, "
                        + "semantic overreach is equivalent to the absence of that license. "
                        + "The argument is constructive and uses neither closure decidability "
                        + "nor double-negation elimination.")),
                Paragraph(Text(
                    "This discharges obligation 57.3-D from definition-escape-completion-theory "
                        + "atom generic-residual-6a153578be42b0dc05d1bf74fa4fe146f63b6fc6a6e6"
                        + "cee245ad9a9835653ca4."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula frame = F.Id("S");
        Formula report = F.Id("report");
        Formula oldDomain = F.Id("J");
        Formula reportedDomain = Call("reportedDomain", report);
        Formula strictExpansion =
            Call("SemanticStrictSubset", frame, oldDomain, reportedDomain);
        Formula scopeExact = Seq(
            Call("claimScope", frame, Call("claim", report)),
            Sp, Eq, Sp, oldDomain);
        Formula overreach = Call("SemanticOverreach", frame, report, oldDomain);
        Formula closure = Call("OverreachClosure", frame, report, oldDomain);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            frame, Comma, Sp,
            report, Comma, Sp,
            oldDomain, Comma, RowBreak, Grp(),
            strictExpansion, Sp, Rightarrow, RowBreak, Grp(),
            scopeExact, Sp, Rightarrow, RowBreak, Grp(),
            Open, overreach, Sp, Iff, Sp, Neg, Sp, closure, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
