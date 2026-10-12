using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums.LanglandsFirstMainLemma;

internal sealed class SupplierPreludeDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/epsilonfml2026hassedavenport");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compatibility metadata and the shared Mathlib import in the supplier closure.",
        H("Supplier prelude"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("supplier-prelude-version"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/Prelude.blueprintScaffoldVersion"),
                H("Compatibility identifier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "blueprintScaffoldVersion is a String constant with value "
                        + "epsilon_FML-2026-08-20. The other retained compatibility definitions "
                        + "are plannedModuleCount = 108, authoritativeManuscript = "
                        + "references/epsilon_FML.tex, and PendingTask = True. These are metadata, "
                        + "not mathematical theorems or evidence that a pending task is solved."))),
                DescribeRole.Definition),
            Paragraph(Text(
                "FiniteProducts and Valuation import Prelude, which imports Mathlib. "
                    + "This import path places Prelude in the HasseDavenportLift supplier closure; "
                    + "the four compatibility constants are not used in the lifting proof.")),
            Paragraph(Text(
                "Source: epsilon_FML at immutable commit "
                    + "b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed, "
                    + "LanglandsFirstMainLemma/Prelude.lean; Apache-2.0. "
                    + "The exact license and original source hashes are in "
                    + "Library/Arith/epsilonfml2026hassedavenport.md.")),
            Paragraph(Text(
                "The supplier's finite-field character/norm/trace escape audit remains "
                    + "unfinished under https://github.com/the-omega-institute/trureturing/issues/5214. "
                    + "This compatibility metadata supplies no mathematical or audit result.")))));
}
