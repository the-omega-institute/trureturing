using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Scattering;

internal sealed class ScatteringRatioCompletionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/Scattering/ScatteringRatioCompletion.scattering_ratio_completion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A scattering-ratio reading and right-shift normalization uniquely recover a nonzero "
            + "meromorphic function and its completed global representative.",
        H("Scattering-Ratio Completion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("scattering-ratio-completion"),
                DeclarationHandle.Create(Declaration),
                H("Scattering data and right normalization determine the global function"),
                StatementSource.FromAuthor(CompletionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For nonzero normal-form meromorphic functions F and G, the local "
                            + "reading R[F](s) is F(2s-1)/F(2s), with meromorphic quotients "
                            + "represented canonically at their discrete exceptional sets. "
                            + "RightNormalized(F,G) is exactly convergence of F/G to one along "
                            + "every sequence z+n.")),
                    Paragraph(Text(
                        "The displayed conclusion has four separate leaves. It proves F=G, "
                            + "existence of a candidate in the recovery fiber, uniqueness of "
                            + "every such candidate, and equality of the selected gauge "
                            + "completion with F. Thus the existence and uniqueness content of "
                            + "unique recovery is not compressed into uniqueness alone.")),
                    Paragraph(Text(
                        "The proof first converts equality of scattering readings into "
                            + "one-periodicity of the normal-form gauge F/G away from the "
                            + "discrete zero and pole sets, then uses meromorphic continuation "
                            + "to make that identity global. Periodicity and the right-shift "
                            + "limit force the gauge to be one. No Riemann hypothesis or other "
                            + "unproved conjecture is assumed."))),
                DescribeRole.Theorem))));

    private static Formula CompletionFormula()
    {
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula functionSpace = Seq(complex, Sp, To, Sp, complex);
        Formula original = F.Id("F");
        Formula candidate = F.Id("G");
        Formula recovered = F.Id("Q");
        Formula readingEquality = Seq(
            Call("scatteringRatio", original), Sp, Eq, Sp,
            Call("scatteringRatio", candidate));
        Formula normalized = Call("RightNormalized", original, candidate);
        Formula recovery = Call("RecoveryFiber", original, recovered);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, original, Comma, Sp, candidate, Colon, Sp, functionSpace, Comma,
            RowBreak, Grp(),
            Call("NonzeroMeromorphic", original), Sp, Land, Sp,
            Call("NonzeroMeromorphic", candidate), Sp, Land, RowBreak, Grp(),
            readingEquality, Sp, Land, Sp, normalized, Sp, Rightarrow, RowBreak, Grp(),
            Open, original, Sp, Eq, Sp, candidate, Close, Sp, Land, RowBreak, Grp(),
            Open, Exists, Sp, recovered, Colon, Sp, functionSpace, Comma, Sp,
            recovery, Close, Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, recovered, Colon, Sp, functionSpace, Comma, Sp,
            recovery, Sp, Rightarrow, Sp, recovered, Sp, Eq, Sp, original, Close,
            Sp, Land, RowBreak, Grp(),
            Open, Call("gaugeCompletion", original), Sp, Eq, Sp, original, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
