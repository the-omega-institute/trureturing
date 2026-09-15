using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Spacetime;

internal sealed class AllSetZeckendorfHereditaryFinitenessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hereditary Finiteness of Zeckendorf Set Codes.",
        H("Hereditary Finiteness of Zeckendorf Set Codes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("all-set-zeckendorf-hereditary-finiteness"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/AllSetZeckendorfHereditaryFiniteness.enc_isHF_iff"),
                H("Preservation and reflection of hereditary finiteness"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In any universe, a set has rank less than omega if and only if its recursive "
                    + "Zeckendorf encoding has rank less than omega. Natural leaves are pairs of "
                    + "finite ordinals and finite digit graphs. For every other set, the encoding "
                    + "pairs tag one with the encodings of its members. Membership induction and "
                    + "injectivity transfer finiteness of the member set in both directions."))),
                DescribeRole.Theorem))));
}
