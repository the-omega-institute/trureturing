using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Solenoid.Connectivity;

internal sealed class CharacterCompletionDualityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Profinite and solenoid completions recover their rational continuous character groups.",
        H("Character Groups of the Two Completions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("completion-carriers-recover-their-rational-character-groups"),
                DeclarationHandle.Create(
                    "D5/S1/Solenoid/Connectivity/CharacterCompletionDuality."
                        + "character_completion_duality"),
                H("The two completion character loops close"),
                StatementSource.FromAuthor(CharacterDualityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A continuous character of the compatible-residue profinite integers is "
                            + "determined by its value at the dense integer generator. Finite-residue "
                            + "factorization makes that value a rational phase, and explicit residue "
                            + "characters realize every rational phase modulo integers. The resulting "
                            + "additive equivalence is characterized by this evaluation equation.")),
                    Paragraph(Text(
                        "For the universal solenoid, the frozen rational-slope equivalence is reused "
                            + "directly. Its inverse computation equation says that reconstructing a "
                            + "coordinate character from the recovered rational slope returns the "
                            + "original continuous character.")),
                    Paragraph(Text(
                        "Repository body-shape search found the finite-residue factorization and the "
                            + "complete solenoid classification, but no profinite rational-phase "
                            + "equivalence. Pinned Mathlib contributes generic range equivalences only; "
                            + "it has no exact classification on these carriers."))),
                DescribeRole.Theorem))));

    private static Formula CharacterDualityFormula()
    {
        Formula profiniteCharacter = F.Id("chi");
        Formula solenoidCharacter = F.Id("psi");
        Formula profiniteCharacterType = Call(
            "ContinuousAddCharacters", F.Id("ProfiniteIntegers"), F.Id("UnitAddCircle"));
        Formula solenoidCharacterType = Call(
            "ContinuousAddCharacters", F.Id("UniversalSolenoid"), F.Id("UnitAddCircle"));

        return Disp(Seq(
            Open, Forall, Sp, profiniteCharacter, Colon, Sp, profiniteCharacterType, Comma, Sp,
            Call("rationalCircleEmbedding",
                Call("profiniteCharacterEquivRationalCircle", profiniteCharacter)),
            Sp, Eq, Sp, Call("profiniteCharacterAtOne", profiniteCharacter), Close,
            Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, solenoidCharacter, Colon, Sp, solenoidCharacterType, Comma, Sp,
            Call("rationalCharacterHom", Call("characterEquivRational", solenoidCharacter)),
            Sp, Eq, Sp, solenoidCharacter, Close, Dot));
    }
}
