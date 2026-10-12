using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums.LanglandsFirstMainLemma.LocalField;

internal sealed class SupplierResidueFieldDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/epsilonfml2026hassedavenport");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical residue fields and the actual algebraic norm and trace used by character pullback.",
        H("Residue fields, trace and norm"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("supplier-residue-norm"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/LocalField/ResidueField.residueNorm"),
                H("Algebraic norm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For fields k and K, a finite underlying type K, and Algebra k K, "
                        + "residueNorm k K is the multiplicative map Algebra.norm k from K to k. "
                        + "It is the actual algebraic norm; the name does not require k and K "
                        + "to be presented as residue fields of local fields."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("supplier-residue-trace"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/LocalField/ResidueField.residueTrace"),
                H("Algebraic trace"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Under the same hypotheses, residueTrace k K is the k-linear map "
                        + "Algebra.trace k K. After the inclusion into K, trace is the sum and "
                        + "norm is the product of x^(|k|^i) for 0 ≤ i < Module.finrank k K. "
                        + "The module also supplies their composition laws in scalar towers."))),
                DescribeRole.Definition),
            Paragraph(Text(
                "CharacterAPI uses residueNorm in normMulChar and residueTrace in traceAddChar. "
                    + "HasseDavenportLift then evaluates these pullbacks in "
                    + "gaussPolynomialWeight_minpoly_power and in the final lift. The local-field "
                    + "part of this module separately defines ResidueField F as the canonical "
                    + "valuation-ring quotient and reduction as congruence modulo lattice F 1; "
                    + "Extension imports that interface as well.")),
            Paragraph(Text(
                "Source: epsilon_FML at immutable commit "
                    + "b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed, "
                    + "LanglandsFirstMainLemma/LocalField/ResidueField.lean; Apache-2.0. "
                    + "The exact license and original source hashes are in "
                    + "Library/Fourier/epsilonfml2026hassedavenport.md. These are attributed "
                    + "upstream definitions and results, not an open-problem resolution.")),
            Paragraph(Text(
                "Supplier escape registration remains unfinished under "
                    + "https://github.com/the-omega-institute/trureturing/issues/5214: the original "
                    + "finite-field character/norm/trace telescope has no supplied faithful enrolled "
                    + "template with compiled audit evidence. This narrative does not complete that audit.")))));
}
