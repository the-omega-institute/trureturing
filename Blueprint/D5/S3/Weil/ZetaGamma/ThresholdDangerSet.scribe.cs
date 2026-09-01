using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma;

internal sealed class ThresholdDangerSetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var reals = Seq(Mathbb, Grp(F.Id("R")));
        var multiplier = F.Id("m");
        var threshold = F.Id("a");
        var xi = F.Id("xi");
        var dangerSet = Call("thresholdDangerSet", multiplier, threshold);
        var setBuilder = Seq(
            OpenBrace, xi, Sp, InMacro, Sp, reals, Sp, Bar, Sp,
            Call("m", xi), Sp, Lt, Sp, threshold, CloseBrace);
        var statement = Disp(new Formula.Aligned([
            Seq(Forall, Sp, multiplier, Colon, Sp, reals, Sp, Mapsto, Sp, reals,
                Comma, Sp, threshold, Colon, Sp, reals, Comma),
            Seq(D(0), Sp, Lt, Sp, threshold, Sp, Rightarrow, Sp,
                dangerSet, Sp, Eq, Sp, setBuilder, Dot),
        ]));

        return DocumentDefinition.Create(ScribeNode.Create(
            "A positive threshold defines the strict sublevel danger set of an abstract real "
                + "multiplier.",
            H("Threshold Danger Set"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("threshold-danger-set"),
                    DeclarationHandle.Create(
                        "D5/S3/Weil/ZetaGamma/ThresholdDangerSet."
                            + "threshold_danger_set_definition"),
                    H("A danger set is a strict multiplier sublevel"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The multiplier is an abstract real-valued parameter because the "
                                + "digested definition does not define its multiplier locally. "
                                + "The positivity premise is retained exactly.")),
                        Paragraph(Text(
                            "The zero multiplier at threshold one proves realizable "
                                + "nonemptiness, while the constant-one multiplier at the same "
                                + "threshold proves that the construction can also be empty.")),
                        Paragraph(Text(
                            "Repository searches found only a private abstract confinement "
                                + "helper and a public theorem for a specific completed-zeta "
                                + "multiplier. Pinned Mathlib and third-party package searches "
                                + "found no matching public strict-sublevel constructor."))),
                    DescribeRole.Theorem))));
    }
}
