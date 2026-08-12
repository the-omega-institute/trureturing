using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer;

internal sealed class CenterOperationalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The operational center of a finite cyclic observer window consists exactly of constant observables.",
        H("Operational Characterization of the Center"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zero-perturbation-characterizes-the-operational-center"),
                DeclarationHandle.Create("D5/S3/Observer/CenterOperational.center_iff_const"),
                H("Zero perturbation characterizes the operational center"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    Forall, Sp, F.Id("M"), InMacro, Sp,
                                    Mathbb, Grp(F.Id("N")), Underscore, Grp(Gt, D(0)), Comma, RowBreak,
                                    Forall, Sp, F.Id("f"), Colon, Sp,
                                    Operatorname, Grp(F.Id("ZMod")), Open, F.Id("M"), Close,
                                    To, Sp, Mathbb, Grp(F.Id("C")), Comma, RowBreak,
                                    F.Id("L"), Underscore, Grp(Plus, D(1)),
                                    Open, F.Id("f"), Close, Eq, Sp, D(0),
                                    Sp, Leftrightarrow, Sp,
                                    Exists, Sp, F.Id("c"), InMacro, Sp,
                                    Mathbb, Grp(F.Id("C")), Comma, Esc,
                                    F.Id("f"), Eq, Sp,
                                    Open, F.Id("i"), Mapsto, Sp, F.Id("c"), Close, Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "Let M be positive and let f be a complex-valued observable on the " +
                                        "cyclic window ZMod M. The seminorm L for translation by one measures " +
                                        "the largest pointwise update defect. Its kernel is the operational " +
                                        "center considered here.")),
                                    Paragraph(Text(
                                        "The established seminorm-kernel theorem first identifies zero " +
                                        "perturbation with invariance under translation by one. The existing " +
                                        "update-defect equivalence transfers that condition to zero defect, and " +
                                        "the cyclic-window characterization then gives a scalar c for which f " +
                                        "is the constant function with value c. Conversely, every constant " +
                                        "observable lies in the kernel. The result introduces no larger operator " +
                                        "algebra or independent notion of center."))),
                DescribeRole.Theorem
            ))));
}
