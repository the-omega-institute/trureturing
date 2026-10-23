using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums.LanglandsFirstMainLemma.LocalField;

internal sealed class SupplierLatticesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/epsilonfml2026hassedavenport");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer-indexed valuation lattices and their reduction at depth one.",
        H("Fractional valuation lattices"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("supplier-first-lattice-maximal-ideal"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/LocalField/Lattices.mem_lattice_one_iff_mem_maximalIdeal"),
                H("The first lattice is the maximal ideal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a nonarchimedean local field F with its valuative relation and topology, "
                        + "ringOfIntegers F is the canonical valuation subring. The submodule "
                        + "lattice F n consists of x with n ≤ ord F x, for every integer n. "
                        + "For an integral element x, its image in F belongs to lattice F 1 "
                        + "if and only if x belongs to the maximal ideal of ringOfIntegers F. "
                        + "Integer-valued order turns the bound 1 ≤ ord(x) into positive order, "
                        + "which is precisely maximal-ideal membership."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "UnitFiltration consumes this equivalence to identify depth-one units with "
                    + "principal units. ResidueField consumes it in residueMap_eq_zero_iff, "
                    + "identifying reduction modulo the maximal ideal with reduction modulo "
                    + "lattice F 1. ResidueField is imported by CharacterAPI, which is imported "
                    + "by HasseDavenportLift. This local-field reduction interface is retained "
                    + "in the supplier's import closure.")),
            Paragraph(Text(
                "Source: epsilon_FML at immutable commit "
                    + "b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed, "
                    + "LanglandsFirstMainLemma/LocalField/Lattices.lean; Apache-2.0. "
                    + "The exact license and original source hashes are in "
                    + "Library/Fourier/epsilonfml2026hassedavenport.md. This is attributed "
                    + "upstream support, not a new theorem or open-problem resolution.")),
            Paragraph(Text(
                "Supplier escape registration remains unfinished under "
                    + "https://github.com/the-omega-institute/trureturing/issues/5214: the original "
                    + "finite-field character/norm/trace telescope has no supplied faithful enrolled "
                    + "template with compiled audit evidence. This narrative does not complete that audit.")))));
}
