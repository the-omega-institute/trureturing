using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics;

internal sealed class SolenoidCharacterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S1/Dynamics/SolenoidCharacter",
            "Continuous universal-solenoid characters are exactly rational coordinate characters."),
        H("Characters of the Universal Solenoid"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("continuous-solenoid-characters-are-rational"),
                H("Continuous solenoid characters have unique rational slopes"),
                LeanTheorem(
                    "D5/S1/Dynamics/SolenoidCharacter."
                    + "continuous_solenoid_characters_are_rational"),
                Disp(Seq(
                    Operatorname, Grp(F.Id("Bijective")), Open,
                    Operatorname, Grp(F.Id("rationalCharacterHom")), Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "For a reduced rational a/m, the corresponding character evaluates "
                        + "the m-th circle coordinate and multiplies it by a. The construction "
                        + "is additive in the rational slope. Conversely, continuity of an "
                        + "arbitrary character gives a finite coordinate whose kernel it kills. "
                        + "Restricting the character to the dense real flow and lifting through "
                        + "the real covering of the unit additive circle produces a continuous "
                        + "additive real map. Its slope times the killed coordinate index is an "
                        + "integer, so the slope is rational. Density proves equality on the "
                        + "whole solenoid, and a half-period argument proves uniqueness.")),
                    Paragraph(Text(
                        "The pinned library was searched before construction. It provides "
                        + "AddCircle.isCoveringMap_coe, "
                        + "IsCoveringMap.existsUnique_continuousMap_lifts, map_real_smul, "
                        + "AddCircle.coe_eq_zero_iff, and the finite-circle torsion lemmas "
                        + "AddCircle.nsmul_eq_zero_iff and ZMod.toAddCircle. It does not provide "
                        + "a universal-solenoid dual classification or a packaged classification "
                        + "of continuous unit-circle endomorphisms. The deposited result is "
                        + "therefore a new proof assembled from those library primitives, not a "
                        + "thin wrapper. The source atom carries no numerical certificate.")))
            ))));
}
