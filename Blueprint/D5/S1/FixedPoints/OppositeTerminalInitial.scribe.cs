using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.FixedPoints;

internal sealed class OppositeTerminalInitialDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Terminal objects become initial objects in the opposite category.",
        H("Terminal and Initial Objects Under Opposites"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("terminal-object-is-initial-after-taking-opposites"),
                DeclarationHandle.Create(
                    "D5/S1/FixedPoints/OppositeTerminalInitial.terminal_iff_initial_op"),
                H("Terminal objects and opposite initial objects coincide"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("X"), InMacro, Sp, F.Id("C"), Comma, Esc,
                    Operatorname, Grp(F.Id("Nonempty")), Open,
                    Operatorname, Grp(F.Id("IsTerminal")), Open, F.Id("X"), Close, Close,
                    Sp, Leftrightarrow, Sp,
                    Operatorname, Grp(F.Id("Nonempty")), Open,
                    Operatorname, Grp(F.Id("IsInitial")), Open,
                    Operatorname, Grp(F.Id("op")), Open, F.Id("X"), Close, Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X be an object of an arbitrary category C. The existence of the "
                            + "terminal-object structure on X, expressed propositionally by "
                            + "Nonempty, is equivalent after reversing all arrows to the existence "
                            + "of the initial-object structure on the opposite of X. The two "
                            + "structures record the same unique-morphism property with every "
                            + "arrow reversed.")),
                    Paragraph(Text(
                        "The pinned Mathlib source was searched before proving. Its declarations "
                            + "IsTerminal.op and IsInitial.unop are exactly the two directions, so "
                            + "the Lean theorem only composes those library results and does not "
                            + "reconstruct the universal-property proof.")),
                    Paragraph(Text(
                        "The formal scope is the first categorical clause of source remark 27.17: "
                            + "terminal and initial objects exchange under passage to the opposite "
                            + "category. It does not formalize the later final-coalgebra, temporal, "
                            + "or interpretive claims in that atom."))),
                DescribeRole.Theorem))));
}
