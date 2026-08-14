using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Symmetry;

internal sealed class MirrorPairEnvelopeMonotonicityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive-slope mirror-pair envelope is strictly increasing on nonnegative inputs.",
        H("Mirror-Pair Envelope Monotonicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-slope-mirror-pair-envelope-is-strictly-increasing"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Symmetry/MirrorPairEnvelopeMonotonicity."
                    + "mirror_pair_envelope_strictMonoOn"),
                H("The positive-slope mirror-pair envelope is strictly increasing"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, Beta, InMacro, Mathbb, Grp(F.Id("R")), Comma, Esc,
                    Beta, Gt, Frac, Grp(D(1)), Grp(D(2)), Sp, Rightarrow, Sp,
                    Forall, Sp, F.Id("u"), Comma, F.Id("v"), InMacro,
                    OpenBracket, D(0), Comma, Infty, Close, Comma, Esc,
                    F.Id("u"), Lt, F.Id("v"), Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("exp")), Open,
                    Open, Beta, Minus, Frac, Grp(D(1)), Grp(D(2)), Close,
                    F.Id("u"), Close,
                    Sp, Plus, Sp,
                    Operatorname, Grp(F.Id("exp")), Open, Minus,
                    Open, Beta, Minus, Frac, Grp(D(1)), Grp(D(2)), Close,
                    F.Id("u"), Close,
                    Sp, Lt, Sp,
                    Operatorname, Grp(F.Id("exp")), Open,
                    Open, Beta, Minus, Frac, Grp(D(1)), Grp(D(2)), Close,
                    F.Id("v"), Close,
                    Sp, Plus, Sp,
                    Operatorname, Grp(F.Id("exp")), Open, Minus,
                    Open, Beta, Minus, Frac, Grp(D(1)), Grp(D(2)), Close,
                    F.Id("v"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For beta greater than one half, the slope beta - 1/2 is positive. "
                        + "Multiplication by that slope preserves the order of nonnegative inputs, "
                        + "and the frozen envelope identity rewrites both sides as twice the "
                        + "hyperbolic cosine. Mathlib's strict monotonicity theorem for cosh on "
                        + "nonnegative arguments then proves the displayed strict inequality.")),
                    Paragraph(Text(
                        "This is a continuation of the earlier envelope identity and closes only "
                        + "the strict-monotonicity clause. The stated numerical value near 3.62, "
                        + "its numerical certificate, and the semantic conservation and zero-pair "
                        + "interpretations remain unresolved."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Zeros/MirrorPairEnvelope")),
        ]));
}
