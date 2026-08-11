using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics;

internal sealed class ProfiniteIntegersDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef RibesZalesskii =
        LibraryNoteRef.Create("D5/L/Dynamics/ribeszalesskii2010profinite");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Natural numbers embed injectively and densely in the compatible-residue model of the profinite integers.",
        H("Natural Numbers in the Profinite Integers"),
        Blocks(
                        Describe.Lean(
                DescribeId.Create("profinite-integers-as-compatible-residue-readings"),
                DeclarationHandle.Create(
                    "D5/S1/Dynamics/ProfiniteIntegers.ProfiniteIntegers"),
                H("Profinite integers are compatible residue readings"),
                StatementSource.FromAuthor(FormulaDsl.Disp(FormulaDsl.Id("ProfiniteIntegers"))),
                AssessedProvenance.FromLiterature(RibesZalesskii),
                Blocks(Paragraph(Text(
                    "A point assigns a residue modulo every positive integer. Whenever one "
                    + "modulus divides another, reduction of the finer reading equals the "
                    + "coarser reading. Positive moduli are indexed canonically by m + 1, "
                    + "so the formal product contains no zero-modulus coordinate."))),
                DescribeRole.Definition),
                        Describe.Lean(
                DescribeId.Create("natural-numbers-embed-injectively-and-densely"),
                DeclarationHandle.Create(
                    "D5/S1/Dynamics/ProfiniteIntegers.nat_embedding_injective_and_dense"),
                H("Natural numbers embed injectively and densely"),
                StatementSource.FromAuthor(new Formula.Logic(
                    Call("Injective", Id("natEmbedding")),
                    FormulaLogicOperator.And,
                    Call("DenseRange", Id("natEmbedding")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Distinct natural numbers are separated by the coordinate whose "
                        + "modulus is one larger than their maximum. For density, a basic "
                        + "product neighborhood constrains only finitely many moduli. Their "
                        + "product is a common multiple, and the compatible reading at that "
                        + "modulus has a natural representative that realizes every "
                        + "constrained coordinate simultaneously.")),
                    Paragraph(Text(
                        "Pinned Mathlib was searched before proving. It provides density of "
                        + "the canonical image of an arbitrary group in its abstract "
                        + "profinite completion, but no theorem that the natural numbers are "
                        + "dense in the profinite completion of the integers. The repository "
                        + "therefore proves the finite-window representative directly rather "
                        + "than restating the upstream integer-image theorem."))),
                DescribeRole.Theorem))));

    private static LeanDeclarationRef LeanDefinition(string value) =>
        LeanDeclarationRef.Create(
            value,
            expectedKind: LeanDeclarationKind.Definition,
            requireNoSorry: true);
}
