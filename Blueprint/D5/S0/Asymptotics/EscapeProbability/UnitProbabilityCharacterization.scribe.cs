using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.EscapeProbability;

internal sealed class UnitProbabilityCharacterizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unit escape probability exactly characterizes fixed-point-free twists on nonempty address sets.",
        H("Unit Escape Probability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("escape-probability-one-iff-fixed-point-free"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/EscapeProbability/UnitProbabilityCharacterization."
                        + "escape_probability_eq_one_iff_fixed_point_free"),
                H("Escape probability one characterizes fixed-point-free twists"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("Y"), Comma, Sp,
                    OpenBracket, Operatorname, Grp(F.Id("Fintype")), Sp, F.Id("Y"),
                    CloseBracket, Sp,
                    OpenBracket, Operatorname, Grp(F.Id("Nonempty")), Sp, F.Id("Y"),
                    CloseBracket, Comma, Sp,
                    Forall, Sp, F.Id("f"), Colon, Sp, F.Id("Y"), Sp, To, Sp, F.Id("Y"),
                    Comma, Sp,
                    Forall, Sp, F.Id("A"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    D(0), Sp, Lt, Sp, F.Id("A"), Sp, Rightarrow, Sp,
                    Open,
                    Call("escapeProbability", Call("Fin", F.Id("A")), F.Id("f")),
                    Sp, Eq, Sp, D(1),
                    Sp, Iff, Sp,
                    Call("card", Call("Fix", F.Id("f"))), Sp, Eq, Sp, D(0),
                    Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The frozen closed form shows that probability one forces the "
                            + "fixed-point ratio to vanish when the address set is nonempty. "
                            + "Conversely, the existing fixed-point-free theorem gives unit "
                            + "escape probability directly.")),
                    Paragraph(Text(
                        "Repository search found only the sufficient direction. Pinned Mathlib "
                            + "supplies the nonnegative power-one characterization and the "
                            + "elementary subtraction and division zero laws used in the converse."))),
                DescribeRole.Theorem)),
        []));
}
