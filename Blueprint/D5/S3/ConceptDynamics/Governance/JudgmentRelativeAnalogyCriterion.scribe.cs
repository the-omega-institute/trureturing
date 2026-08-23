using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Governance;

internal sealed class JudgmentRelativeAnalogyCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Similarity supports equal judgments only when it preserves judgment distinctions.",
        H("Judgment-Relative Analogy Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("judgment-relative-analogy-criterion"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Governance/JudgmentRelativeAnalogyCriterion."
                        + "judgment_relative_analogy_criterion"),
                H("Relevant analogy criterion"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, F.Id("X"), Comma, Sp, F.Id("B"), Comma, Sp,
                    F.Id("Y"), Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma,
                    RowBreak, Grp(),
                    F.Id("R"), Colon, Sp, F.Id("X"), Sp, To, Sp, F.Id("B"), Comma, Sp,
                    F.Id("J"), Colon, Sp, F.Id("X"), Sp, To, Sp, F.Id("Y"), Comma,
                    RowBreak, Grp(),
                    Open, Operatorname, Grp(F.Id("Refines")), Open,
                    Operatorname, Grp(F.Id("canonicalTargetReadout")), Open, F.Id("J"),
                    Close, Comma, Sp, F.Id("R"), Close, Sp, Longrightarrow, RowBreak, Grp(),
                    Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
                    F.Id("R"), Open, F.Id("x"), Close, Sp, Eq, Sp,
                    F.Id("R"), Open, F.Id("y"), Close, Sp, Longrightarrow, Sp,
                    F.Id("J"), Open, F.Id("x"), Close, Sp, Eq, Sp,
                    F.Id("J"), Open, F.Id("y"), Close, Close, Sp, Land, RowBreak, Grp(),
                    Open, Open, Exists, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
                    F.Id("R"), Open, F.Id("x"), Close, Sp, Eq, Sp,
                    F.Id("R"), Open, F.Id("y"), Close, Sp, Land, Sp,
                    F.Id("J"), Open, F.Id("x"), Close, Sp, Neq, Sp,
                    F.Id("J"), Open, F.Id("y"), Close, Close, Sp, Longrightarrow, RowBreak,
                    Grp(), Neg, Sp, Operatorname, Grp(F.Id("Refines")), Open,
                    Operatorname, Grp(F.Id("canonicalTargetReadout")), Open, F.Id("J"),
                    Close, Comma, Sp, F.Id("R"), Close, Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The canonical judgment target records exactly the distinctions made by J. "
                            + "If it factors through the case-similarity readout R, equal R-values "
                            + "force equal judgments.")),
                    Paragraph(Text(
                        "A pair of cases with the same similarity value and different judgments is "
                            + "therefore an explicit obstruction to that factorization. Similarity "
                            + "is consequently assessed relative to the judgment target whose "
                            + "distinctions it must preserve."))),
                DescribeRole.Theorem))));
}
