using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums.LanglandsFirstMainLemma.LocalField;

internal sealed class SupplierUnitFiltrationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/epsilonfml2026hassedavenport");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The local-unit filtration and its first principal-unit layer.",
        H("Local units and principal units"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("supplier-first-principal-unit-layer"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/LocalField/UnitFiltration.unitFiltration_one_eq_principalUnitGroup"),
                H("Depth one equals the canonical principal-unit group"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a nonarchimedean local field F with its valuative relation and topology, "
                        + "unitFiltration F 0 is the canonical valuation-ring unit subgroup of Fˣ. "
                        + "At positive depth n, membership means ord F (u - 1) ≥ n. "
                        + "The theorem identifies unitFiltration F 1 with the canonical "
                        + "valuation subring's principalUnitGroup. The depth-zero layer is "
                        + "kept distinct from the positive-depth congruence condition."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "ResidueField uses this equality in residueUnits_ker: the kernel of unit "
                    + "reduction is the depth-one layer viewed inside the depth-zero group. "
                    + "Its residueUnits_coe also uses unitGroupMulEquivRingOfIntegers. "
                    + "ResidueField → CharacterAPI → HasseDavenportLift is the remaining "
                    + "import path. The retained local-unit quotient infrastructure does not "
                    + "add a local-field hypothesis to the finite-field lifting theorem.")),
            Paragraph(Text(
                "Source: epsilon_FML at immutable commit "
                    + "b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed, "
                    + "LanglandsFirstMainLemma/LocalField/UnitFiltration.lean; Apache-2.0. "
                    + "The exact license and original source hashes are in "
                    + "Library/Fourier/epsilonfml2026hassedavenport.md. This is attributed "
                    + "upstream support, not a new theorem or open-problem resolution.")),
            Paragraph(Text(
                "Supplier escape registration remains unfinished under "
                    + "https://github.com/the-omega-institute/trureturing/issues/5214: the original "
                    + "finite-field character/norm/trace telescope has no supplied faithful enrolled "
                    + "template with compiled audit evidence. This narrative does not complete that audit.")))));
}
