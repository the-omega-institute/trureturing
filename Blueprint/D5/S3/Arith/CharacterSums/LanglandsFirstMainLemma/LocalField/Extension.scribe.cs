using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums.LanglandsFirstMainLemma.LocalField;

internal sealed class SupplierExtensionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/epsilonfml2026hassedavenport");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Norms and conjugates in the extension module retained by the supplier imports.",
        H("Extension norm and conjugates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("supplier-galois-conjugates-norm"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/LocalField/Extension.galoisConjugates_prod"),
                H("The norm is the product of Galois conjugates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For fields F and K with Algebra F K, FiniteDimensional F K and IsGalois F K, "
                        + "galoisConjugates F K x is the multiset of σ(x) indexed by Gal(K/F). "
                        + "For every x in K its product equals algebraMap F K (norm F K x), "
                        + "where norm is Algebra.norm. Conjugates are counted by automorphisms "
                        + "with multiplicity. The parallel sum identity gives Algebra.trace, "
                        + "and the multiset cardinality is Module.finrank F K."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "HasseDavenportLift directly imports Extension, which imports ResidueField. "
                    + "This is a retained import dependency: the selected lifting proof "
                    + "uses Mathlib's Algebra.norm and Algebra.trace through CharacterAPI "
                    + "and minimal-polynomial identities, without invoking "
                    + "galoisConjugates_prod. The local-field ramification and norm-order "
                    + "results elsewhere in Extension impose no extra hypotheses on the lift.")),
            Paragraph(Text(
                "Source: epsilon_FML at immutable commit "
                    + "b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed, "
                    + "LanglandsFirstMainLemma/LocalField/Extension.lean; Apache-2.0. "
                    + "The exact license and original source hashes are in "
                    + "Library/Fourier/epsilonfml2026hassedavenport.md. This is attributed "
                    + "upstream support, not a new theorem or open-problem resolution.")),
            Paragraph(Text(
                "Supplier escape registration remains unfinished under "
                    + "https://github.com/the-omega-institute/trureturing/issues/5214: the original "
                    + "finite-field character/norm/trace telescope has no supplied faithful enrolled "
                    + "template with compiled audit evidence. This narrative does not complete that audit.")))));
}
