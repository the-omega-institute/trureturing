using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.SternBrocot;

internal sealed class WordNodesAreReducedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every left-right word carries a unimodular matrix, so every node of the tree is a "
            + "fraction already in lowest terms.",
        H("Word Nodes Are Reduced"),
        Blocks(
            Paragraph(Text(
                "The two generators of the tree are unimodular, and the matrix product "
                    + "preserves the unimodular equation. Every finite word of left and right "
                    + "steps therefore carries a unimodular matrix, and the lower row of a "
                    + "unimodular matrix is coprime. That is the tree's prototype primality "
                    + "statement: irreducibility is not checked node by node, it is inherited "
                    + "from the group.")),
            Paragraph(Text(
                "The last conjunct is a non-collapse witness rather than a further property. "
                    + "Without it the universal statement would be satisfied by a map sending "
                    + "every word to one fixed matrix, which would make the quantifier "
                    + "decoration rather than content. Along an all-left word the lower-left "
                    + "coordinate equals the word length, so the quantifier ranges over "
                    + "infinitely many distinct nodes.")),
            Describe.Lean(
                DescribeId.Create("every-tree-word-carries-a-reduced-node"),
                DeclarationHandle.Create(
                    "D5/S3/PrimeForms/SternBrocot/WordNodesAreReduced."
                        + "stern_brocot_nodes_are_reduced_package"),
                H("Every tree word carries a reduced node"),
                StatementSource.FromAuthor(ReducedFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The displayed conjunct is the coprimality of the lower row; the package "
                        + "also carries unimodularity, positivity of the lower-right "
                        + "coordinate, and the non-collapse witness."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/PrimeForms/Crossing/ExactPropagation")),
        ]));

    // D() takes individual decimal digits, not a value. Every literal below is a single
    // digit, so no digit-sequence spelling is needed here.
    private static Formula Node(Formula word) =>
        Seq(F.Id("M"), Open, word, Close);

    private static Formula ReducedFormula()
    {
        Formula word = F.Id("w");

        return Disp(Seq(
            Forall, Sp, word, InMacro, Sp,
            Operatorname, Grp(F.Id("List")), Sp, Operatorname, Grp(F.Id("Bool")), Comma, Esc,
            Operatorname, Grp(F.Id("gcd")), Open,
            Node(word), Underscore, Grp(F.Id("d")), Comma, Sp,
            Node(word), Underscore, Grp(F.Id("c")), Close, Sp, Eq, Sp, D(1), Dot));
    }
}
