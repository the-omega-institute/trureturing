using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics;

internal sealed class FiniteProgramLevelSetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Programs over a finite binary alphabet with a bounded description length form a finite level set.",
        H("Finite Program Level Sets"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bounded-binary-programs-form-a-finite-level-set"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/FiniteProgramLevelSet.bounded_programs_finite"),
                H("Bounded binary programs form a finite level set"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("Q"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Operatorname, Grp(F.Id("Finite")), Open, F.Id("boundedPrograms"), Open,
                    F.Id("Q"), Close, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A binary algorithm program is represented by a list over Fin 2, and "
                        + "boundedPrograms Q selects exactly those lists whose length is at most Q. "
                        + "Mathlib's List.finite_length_le supplies the finite-level-set result, "
                        + "so this declaration is a thin wrapper rather than a re-proof.")),
                    Paragraph(Text(
                        "This deposit is a partial closure of clause (a) of source theorem 3.4. "
                        + "The body/value non-finiteness clause (b) and the Levin mixed-cost "
                        + "finiteness clause (c) remain unresolved and are intentionally not claimed."))),
                DescribeRole.Theorem))));
}
