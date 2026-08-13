using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting;

internal sealed class SinglePointPatchDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A single-point update outside a finite record preserves all recorded values while changing the rule.",
        H("Single-Point Patch"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("an-outside-record-update-preserves-consistency"),
                DeclarationHandle.Create(
                    "D5/S0/Rewriting/SinglePointPatch.update_outside_record_preserves_consistency"),
                H("An update outside the record preserves consistency"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("D"), Comma, F.Id("Y"), Comma, Sp,
                    OpenBracket, Operatorname, Grp(F.Id("DecidableEq")),
                    Open, F.Id("D"), Close, CloseBracket, Comma, Esc,
                    Forall, Sp, F.Id("record"), Sp, InMacro, Sp,
                    Operatorname, Grp(F.Id("Finset")), Open, F.Id("D"), Close, Comma, Sp,
                    Forall, Sp, F.Id("prescribed"), Comma, F.Id("rule"), Colon, Sp,
                    F.Id("D"), Sp, To, Sp, F.Id("Y"), Comma, Esc,
                    Forall, Sp, F.Id("a"), Sp, InMacro, Sp, F.Id("D"), Comma, Sp,
                    Forall, Sp, F.Id("b"), Sp, InMacro, Sp, F.Id("Y"), Comma, Esc,
                    Open,
                    Open, Forall, Sp, F.Id("d"), Sp, InMacro, Sp, F.Id("record"), Comma, Sp,
                    F.Id("rule"), Open, F.Id("d"), Close, Sp, Eq, Sp,
                    F.Id("prescribed"), Open, F.Id("d"), Close, Close,
                    Sp, Land, Sp,
                    Neg, Open, F.Id("a"), Sp, InMacro, Sp, F.Id("record"), Close,
                    Sp, Land, Sp,
                    F.Id("b"), Sp, Neq, Sp, F.Id("rule"), Open, F.Id("a"), Close,
                    Close, Sp, Rightarrow, Esc,
                    Open,
                    Open, Forall, Sp, F.Id("d"), Sp, InMacro, Sp, F.Id("record"), Comma, Sp,
                    F.Id("update"), Open, F.Id("rule"), Comma, F.Id("a"), Comma,
                    F.Id("b"), Close, Open, F.Id("d"), Close, Sp, Eq, Sp,
                    F.Id("prescribed"), Open, F.Id("d"), Close, Close,
                    Sp, Land, Sp,
                    F.Id("update"), Open, F.Id("rule"), Comma, F.Id("a"), Comma,
                    F.Id("b"), Close, Sp, Neq, Sp, F.Id("rule"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let record be a finite set of observed positions, prescribed the observed "
                        + "values, and rule a function agreeing with those observations. If a lies "
                        + "outside record and b differs from rule(a), replacing rule(a) by b leaves "
                        + "every recorded value unchanged and produces a function unequal to rule.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies Function.update_of_ne for recorded positions and "
                        + "Function.update_ne_self_iff for the genuine change at a. The theorem is "
                        + "therefore a thin wrapper around the upstream function-update API.")),
                    Paragraph(Text(
                        "This is an honest partial closure of the leading consistency clause in the "
                        + "source corollary. The program-complexity upper bound and the subsequent "
                        + "population-level semantic commentary remain unresolved."))),
                DescribeRole.Theorem))));
}
