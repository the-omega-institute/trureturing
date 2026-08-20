using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Naming.Conservation;

internal sealed class CompletionEmbeddingResidualDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A countable perfect metric space has a negligible image in its completion.",
        H("Residual Complement of the Canonical Completion Image"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("completion-embedding-residual-full-measure"),
                DeclarationHandle.Create(
                    "D5/S0/Naming/Conservation/CompletionEmbeddingResidual."
                    + "completion_embedding_residual_full_measure"),
                H("The canonical completion image has residual full-measure complement"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("N"), Comma, Sp, Mu, Comma, RowBreak, Grp(),
                    OpenBracket, Operatorname, Grp(F.Id("MetricSpace")),
                    Open, F.Id("N"), Close, CloseBracket, Comma, Sp,
                    OpenBracket, Operatorname, Grp(F.Id("Countable")),
                    Open, F.Id("N"), Close, CloseBracket, Comma, Sp,
                    OpenBracket, Operatorname, Grp(F.Id("PerfectSpace")),
                    Open, F.Id("N"), Close, CloseBracket, Comma, RowBreak, Grp(),
                    OpenBracket, Operatorname, Grp(F.Id("NoAtoms")),
                    Open, Mu, Close, CloseBracket, Comma, Sp,
                    OpenBracket, Operatorname, Grp(F.Id("IsProbabilityMeasure")),
                    Open, Mu, Close, CloseBracket, Comma, RowBreak,
                    Operatorname, Grp(F.Id("DenseRange")), Open,
                    F.Id("coe"), Underscore, Grp(F.Id("N")), Close, Sp, Land, RowBreak,
                    Operatorname, Grp(F.Id("PerfectSpace")), Open,
                    Operatorname, Grp(F.Id("Completion")), Open, F.Id("N"), Close,
                    Close, Sp, Land, RowBreak,
                    Operatorname, Grp(F.Id("IsMeagre")), Open,
                    Operatorname, Grp(F.Id("range")), Open,
                    F.Id("coe"), Underscore, Grp(F.Id("N")), Close, Close,
                    Sp, Land, RowBreak,
                    Mu, Open,
                    Operatorname, Grp(F.Id("Completion")), Open, F.Id("N"), Close,
                    Sp, Setminus, Sp, Operatorname, Grp(F.Id("range")), Open,
                    F.Id("coe"), Underscore, Grp(F.Id("N")), Close, Close,
                    Eq, D(1), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The absence of isolated points is assumed for N and proved for its "
                            + "completion. Density alone is clause (i), already carried by the "
                            + "frozen CompletionEmbeddingDense declaration.")),
                    Paragraph(Text(
                        "The proof transfers preperfectness through the canonical embedding. "
                            + "Its dense closure is the whole completion, so the completion is a "
                            + "perfect space. Countability then writes the image as a countable "
                            + "union of nowhere-dense singletons.")),
                    Paragraph(Text(
                        "An atomless measure assigns zero measure to the countable image. "
                            + "Probability normalization therefore gives measure one to its "
                            + "complement.")),
                    Paragraph(Text(
                        "This declaration discharges clauses (ii) and (iii). It does not claim "
                            + "coverage of the residual atom. D5-T0032 remains open because the "
                            + "existing formalization receipt is misbound and may be corrected "
                            + "only through the receipt-correction door."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/Naming/CompletionEmbeddingDense"))]));
}
