using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums.LanglandsFirstMainLemma.LocalField;

internal sealed class SupplierValuationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/epsilonfml2026hassedavenport");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized additive order and the canonical valuation ring of a nonarchimedean local field.",
        H("Normalized local-field order"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("supplier-order-integer-ring"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/LocalField/Valuation.ord_nonneg_iff_mem_integer"),
                H("Nonnegative order is integrality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Let F be a field with a valuative relation, a topology, and "
                        + "IsNonarchimedeanLocalField F. For every x in F, 0 ≤ ord F x if and "
                        + "only if x belongs to the integer subring of ValuativeRel.valuation F. "
                        + "The order is the canonical valuation transported to WithTop ℤ with "
                        + "the negative-logarithm convention: ord(0) = ⊤, ord(1) = 0, products "
                        + "add orders, and uniformizers have order 1. The equivalence identifies "
                        + "its nonnegative cone with Mathlib's existing valuation ring."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "This module imports Mathlib directly. Lattices uses this theorem to prove "
                    + "scalar closure of lattice F n and "
                    + "mem_lattice_zero_iff. UnitFiltration also uses it for integral units. "
                    + "The import path to the lift is Valuation → Lattices → UnitFiltration → "
                    + "ResidueField → CharacterAPI → HasseDavenportLift. The local-field "
                    + "assumptions belong to this support module; the finite-field lift does "
                    + "not impose them on k and K.")),
            Paragraph(Text(
                "Source: epsilon_FML at immutable commit "
                    + "b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed, "
                    + "LanglandsFirstMainLemma/LocalField/Valuation.lean; Apache-2.0. "
                    + "The exact license and original source hashes are in "
                    + "Library/Fourier/epsilonfml2026hassedavenport.md. This is attributed "
                    + "upstream support, not a new theorem or open-problem resolution.")),
            Paragraph(Text(
                "Supplier escape registration remains unfinished under "
                    + "https://github.com/the-omega-institute/trureturing/issues/5214: the original "
                    + "finite-field character/norm/trace telescope has no supplied faithful enrolled "
                    + "template with compiled audit evidence. This narrative does not complete that audit.")))));
}
