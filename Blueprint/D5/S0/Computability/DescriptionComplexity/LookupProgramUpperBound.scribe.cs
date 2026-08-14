using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.DescriptionComplexity;

internal sealed class LookupProgramUpperBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A lookup compiler bounds the least cost of a total program consistent with a record.",
        H("Lookup Program Upper Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("lookup-program-upper-bound"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/DescriptionComplexity/LookupProgramUpperBound.lookup_program_upper_bound"),
                H("A table-lookup program bounds the spectrum bottom"),
                StatementSource.FromAuthor(Disp(Seq(
                    new Formula.Subscript(F.Id("k"), F.Id("min")),
                    Open, F.Id("R"), Close, Sp, Le, Sp,
                    F.Id("K"), Open, F.Id("R"), Close, Sp, Plus, Sp, F.Id("c"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A LookupCompiler assigns each finite record a total program that agrees "
                        + "with the record. Its cost field states that this explicit lookup program "
                        + "uses at most the record-description cost plus a fixed overhead.")),
                    Paragraph(Text(
                        "The spectrum bottom is the least natural-number cost among all total "
                        + "programs consistent with the record. The compiled lookup program is a "
                        + "member of that class, so minimality gives the displayed upper bound.")),
                    Paragraph(Text(
                        "Pinned Mathlib has no matching description-complexity model. The proof "
                        + "therefore keeps the program and consistency semantics explicit while "
                        + "reusing Nat.find_min' for the least-witness inequality."))),
                DescribeRole.Theorem)),
        []));
}
