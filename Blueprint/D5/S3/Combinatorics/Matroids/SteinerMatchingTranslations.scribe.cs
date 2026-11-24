using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class SteinerMatchingTranslationsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/SteinerMatchingTranslations";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGeometry/quackenbush1976steinerloops");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pair completion in a complete Steiner triple system gives perfect matchings on the enlarged point set.",
        H("Matching Translations of a Steiner Triple System"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("steiner-translation"),
                DeclarationHandle.Create(Module + ".translate"),
                H("Translation through a pivot"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Adjoin one point to the finite complete Steiner triple system. Pair it with the pivot. For an original point distinct from the pivot, take the third point of its block with the pivot."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("translation-at-adjoined-point"),
                DeclarationHandle.Create(Module + ".translate_none"),
                H("Translation at the adjoined point"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The translation sends the adjoined point to the pivot."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("translation-at-pivot"),
                DeclarationHandle.Create(Module + ".translate_self"),
                H("Translation at the pivot"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The translation sends the pivot to the adjoined point."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("translation-involution"),
                DeclarationHandle.Create(Module + ".translate_involutive"),
                H("Involution law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The translation applied twice is the identity. The second step uses the same block by uniqueness of pair completion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("translation-fixed-point-free"),
                DeclarationHandle.Create(Module + ".translate_ne_self"),
                H("No fixed points"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Every point moves under the translation. A pivot exchanges with the adjoined point and the other pairs consist of distinct points in a block."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("translation-distinct-pivots"),
                DeclarationHandle.Create(Module + ".translate_ne_translate"),
                H("Distinct partners"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Translations through distinct pivots give different partners at every point. At a point away from both pivots, a common partner would force two distinct blocks to share a pair."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("translation-square"),
                DeclarationHandle.Create(Module + ".translate_special_square"),
                H("The square containing the adjoined point"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For distinct pivots the two translations send the other pivot to a common third point distinct from both pivots. The adjoined point, the two pivots, and their common third point therefore form a square."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("translation-leave"),
                DeclarationHandle.Create(Module + ".translate_deleted_match"),
                H("Restriction to the leave matching"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If the uncovered pairs of the point-deleted packing agree exactly with the partners of a map on retained labels, the translation through the deleted pivot sends each retained point to the corresponding partner. The original block through the deleted pivot excludes its other pair from every retained block by pair uniqueness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("switch-commutation"),
                DeclarationHandle.Create(Module + ".switch_commutes_iff"),
                H("Commutation detects the closing pair"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume the leave partners of the retained packing are given by the map m. For a start a and a retained pivot v distinct from a and m(a), suppose the blocks through the pairs av and m(a)v have respective third labels b and d. The two translations through the deleted point and v commute at the embedded start exactly when d equals m(b). One order reaches d and the other reaches m(b)."))),
                DescribeRole.Theorem))));
}
