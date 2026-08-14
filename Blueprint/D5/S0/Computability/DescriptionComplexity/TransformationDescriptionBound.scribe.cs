using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.DescriptionComplexity;

internal sealed class TransformationDescriptionBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A compiler bounds target description cost by source and transformation costs.",
        H("Transformation Description Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("transformation-description-complexity-bound"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/DescriptionComplexity/TransformationDescriptionBound"
                    + ".transformation_description_complexity_le"),
                H("Compiled transformations have an additive description bound"),
                StatementSource.FromAuthor(Disp(Seq(
                    new Formula.Subscript(F.Id("K"), F.Id("target")),
                    Open, F.Id("y"), Close, Sp, Le, Sp,
                    new Formula.Subscript(F.Id("K"), F.Id("source")),
                    Open, F.Id("x"), Close, Sp, Plus, Sp,
                    new Formula.Subscript(F.Id("K"), F.Id("transform")),
                    Open, F.Id("u"), Close, Sp, Plus, Sp, F.Id("c"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Each description system records a realization relation and a natural-number "
                        + "code cost. An encoder supplies one description of every object, while the "
                        + "displayed complexity is the minimum cost among all realizing codes.")),
                    Paragraph(Text(
                        "The compiler combines a code for u with a code for x. Its correctness field "
                        + "makes the combined code realize y whenever u carries x to y, and its cost "
                        + "field charges at most the two input costs plus the fixed overhead c.")),
                    Paragraph(Text(
                        "The proof extracts minimum-cost source and transformation codes, compiles "
                        + "them, and uses target minimality. The natural-number addition model in the "
                        + "Lean module witnesses that the premises are inhabited at positive cost.")),
                    Paragraph(Text(
                        "Pinned Mathlib and public Lean repositories were searched before proving. "
                        + "No matching description-complexity model or transformation bound was found. "
                        + "The proof reuses Nat.find_min' for the least-witness inequality and keeps "
                        + "the realization and compiler semantics explicit.")),
                    Paragraph(Text(
                        "This is an honest partial closure of the leading forward bound in source "
                        + "proposition 3.5. Its reverse bound, absolute-difference consequence, and "
                        + "logarithmic-tightness construction remain residual and are not asserted."))),
                DescribeRole.Theorem)),
        []));
}
