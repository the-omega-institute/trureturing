using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting;

internal sealed class BinaryPatchFamilyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary choices on distinct off-record slots produce distinct functions that preserve every recorded value.",
        H("Binary Patch Families"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("binary-patches-are-distinct-and-record-consistent"),
                DeclarationHandle.Create(
                    "D5/S0/Rewriting/BinaryPatchFamily.binary_patch_family_injective_and_consistent"),
                H("Binary patches are distinct and preserve the record"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("D"), Comma, F.Id("Y"), Comma, Sp,
                    Forall, Sp, F.Id("ell"), Sp, InMacro, Sp, F.Id("N"), Comma, Sp,
                    Forall, Sp, F.Id("record"), Sp, InMacro, Sp,
                    Operatorname, Grp(F.Id("Finset")), Open, F.Id("D"), Close, Comma, Esc,
                    Forall, Sp, F.Id("prescribed"), Comma, F.Id("base"), Colon, Sp,
                    F.Id("D"), Sp, To, Sp, F.Id("Y"), Comma, Esc,
                    Forall, Sp, F.Id("slot"), Colon, Sp, F.Id("Fin"), Open, F.Id("ell"), Close,
                    Sp, To, Sp, F.Id("D"), Comma, Sp,
                    Forall, Sp, F.Id("twist"), Colon, Sp, F.Id("Y"), Sp, To, Sp,
                    F.Id("Y"), Comma, Esc,
                    Open,
                    Open, Forall, Sp, F.Id("d"), Sp, InMacro, Sp, F.Id("record"), Comma, Sp,
                    F.Id("base"), Open, F.Id("d"), Close, Sp, Eq, Sp,
                    F.Id("prescribed"), Open, F.Id("d"), Close, Close,
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("Injective")), Open, F.Id("slot"), Close,
                    Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("j"), Comma, Sp,
                    Neg, Open, F.Id("slot"), Open, F.Id("j"), Close, Sp, InMacro, Sp,
                    F.Id("record"), Close, Close,
                    Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("y"), Comma, Sp,
                    F.Id("twist"), Open, F.Id("y"), Close, Sp, Neq, Sp, F.Id("y"), Close,
                    Close, Sp, Rightarrow, Esc,
                    Open,
                    Operatorname, Grp(F.Id("Injective")), Open,
                    F.Id("patchedFamily"), Open, F.Id("base"), Comma, F.Id("slot"), Comma,
                    F.Id("twist"), Close, Close,
                    Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("word"), Comma, F.Id("d"), Sp, InMacro, Sp,
                    F.Id("record"), Comma, Esc,
                    F.Id("patchedFamily"), Open, F.Id("base"), Comma, F.Id("slot"), Comma,
                    F.Id("twist"), Comma, F.Id("word"), Close, Open, F.Id("d"), Close,
                    Sp, Eq, Sp, F.Id("prescribed"), Open, F.Id("d"), Close, Close,
                    Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let record be a finite set of observed positions and base a function that "
                        + "agrees with the prescribed observations. An injective slot map places "
                        + "every patch outside record. At each slot a binary word chooses between "
                        + "the base value and its image under a fixed-point-free twist.")),
                    Paragraph(Text(
                        "Evaluating equal patched functions at each designated slot recovers every "
                        + "binary choice, so the patch-family map is injective. Away from the slot "
                        + "range, Mathlib's Function.extend returns base; consequently every member "
                        + "of the family preserves the complete finite record.")),
                    Paragraph(Text(
                        "This is an honest partial closure of the construction clause in source "
                        + "theorem 6.7. Computability of the patched functions, program descriptions, "
                        + "complexity estimates, the budget-dependent word length, and the final "
                        + "asymptotic lower bound remain unresolved."))),
                DescribeRole.Theorem))));
}
