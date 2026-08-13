using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Midline;

internal sealed class AutomaticMidlineDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Half-density unitarity and self-resonance select the same automatic midline.",
        H("Automatic Midline Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("half-density-unitarity-is-equivalent-to-self-resonance"),
                DeclarationHandle.Create(
                    "D5/S3/Midline/AutomaticMidlineDecomposition.half_density_unitarity_iff_self_resonance"),
                H("Half-density unitarity is equivalent to self-resonance"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, F.Id("A"), Comma, Sp,
                    F.Id("M"), Colon, Sp, F.Id("A"), To, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Alpha, InMacro, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    F.Id("s"), InMacro, Mathbb, Grp(F.Id("C")), Comma,
                    RowBreak, Sp,
                    Open, Forall, Sp, F.Id("a"), Comma, Sp,
                    D(0), Le, Sp, F.Id("M"), Open, F.Id("a"), Close, Close, Comma, Sp,
                    Open, Exists, Sp, F.Id("a"), Comma, Sp,
                    F.Id("M"), Open, F.Id("a"), Close, Neq, D(0), Close,
                    RowBreak, Sp, Rightarrow, Sp,
                    Open, Forall, Sp, F.Id("a"), Comma, Sp,
                    Bar, Operatorname, Grp(F.Id("halfDensityCoefficient")), Open,
                    F.Id("M"), Comma, Alpha, Comma, F.Id("s"), Comma, F.Id("a"), Close,
                    Bar, Eq, D(1), Close,
                    RowBreak, Sp, Leftrightarrow, Sp,
                    Operatorname, Grp(F.Id("KernelResonant")), Open,
                    Alpha, Comma, F.Id("s"), Comma, F.Id("s"), Close,
                    Dot, Sp, End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a nonnegative, nontrivial heat spectrum, coordinatewise unit modulus "
                        + "after half-density normalization is equivalent to self-resonance. Both "
                        + "conditions independently characterize the real line at alpha over two.")),
                    Paragraph(Text(
                        "The proof is a thin wrapper over the exact half-density and resonance "
                        + "characterizations in the universal heat-trace module.")),
                    Paragraph(Text(
                        "This is a partial closure of the automatic-midline clause. The square-"
                        + "summability boundary, an independent reflection center, and the named "
                        + "analytic and quasicrystal instances remain open."))),
                DescribeRole.Theorem))));
}
