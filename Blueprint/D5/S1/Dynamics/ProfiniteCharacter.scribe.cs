using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics;

internal sealed class ProfiniteCharacterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Dynamics/ProfiniteCharacter",
                "Continuous profinite-integer characters factor through a finite residue coordinate."),
            H("Continuous Characters of the Profinite Integers"),
            Blocks(
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("continuous-character-factors-through-residue"),
                    H("Every continuous character has finite level"),
                    LeanTheorem(
                        "D5/S1/Dynamics/ProfiniteCharacter."
                        + "continuous_character_factors_through_residue"),
                    Call(
                        "FactorsThroughFiniteResidue",
                        StrataLint.Scribe.FormulaDsl.Id("chi")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(
                        Paragraph(Text(
                            "A basic neighborhood of zero constrains finitely many residue "
                            + "coordinates, whose product supplies one common modulus. "
                            + "Continuity sends the resulting coordinate kernel into a small "
                            + "arc of the circle. Since a subgroup contained in that arc is "
                            + "trivial, the character vanishes on the coordinate kernel and "
                            + "therefore descends to the finite cyclic quotient.")),
                        Paragraph(Text(
                            "The finite quotient character is then determined by its value at "
                            + "one. The pinned library supplies the no-small-subgroup lemma for "
                            + "the circle, the classification of finite-order circle points, "
                            + "and standard finite cyclic characters. It does not supply the "
                            + "profinite finite-level factorization proved here.")))))));
}
