using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Carrier;

internal sealed class GoldenRatioDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S0/Carrier/GoldenRatio",
            "The real golden ratio satisfies its radical, fixed-point, and conjugate identities."),
        H("Golden Ratio Identities"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("radical-fixed-point-and-conjugate-identities"),
                DeclarationHandle.Create(
                    "D5/S0/Carrier/GoldenRatio.golden_ratio_spec"),
                H("Radical, fixed-point, and conjugate identities"),
                StatementSource.FromAuthor(Disp(Seq(Varphi, Sp, Eq, Sp, Frac, Grp(D(1), Sp, Plus, Sp, Sqrt, Grp(D(5))), Grp(D(2)), Sp, Land, Sp, Varphi, Caret, Grp(D(2)), Sp, Eq, Sp, Varphi, Sp, Plus, Sp, D(1), Sp, Land, Sp, D(1), Sp, Minus, Sp, Varphi, Sp, Eq, Sp, Minus, Frac, Grp(D(1)), Grp(Varphi)))),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/koshy2001fibonacci")),
                Blocks(Paragraph(Text(
                    "One kernel-checked conjunction records the radical definition, the quadratic fixed point, and the negative-reciprocal conjugate identity."))),
                DescribeRole.Theorem)),
        [DocumentEdge.NarrativeReference.ToDocument(
            GidRef.Create("D5/S0/Conventions/Notation"))]));
}
