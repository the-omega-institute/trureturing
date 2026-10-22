using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Sequenceability;

internal sealed class ChosenMergeExpansionRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Sequenceability/ChosenMergeExpansionRefutation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A forced internal cut refutes uniform adjacent expansion for a chosen legal merge.",
        H("Chosen merge expansion obstruction"),
        Blocks(
            Node("good", "Proper zero-sum intervals", "Good",
                "Good(w) requires every nonempty proper contiguous interval of w to have nonzero sum. The whole word is exempt, so a total zero is allowed.",
                DescribeRole.Definition),
            Node("expand", "Adjacent expansion", "expand",
                "expand x y replaces the unique merged letter x + y by the adjacent pair x,y in a compressed word.",
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("chosen-merge-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Guarded universal chosen-merge lifting claim"),
                StatementSource.FromAuthor(Disp(F.Id("claim"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every finite A of nonzero group elements with at least three members, "
                        + "and every distinct legal pair a,b whose sum is outside A and nonzero, "
                        + "if the compressed alphabet has a Good permutation then some Good "
                        + "compressed permutation has a Good adjacent expansion in one of the "
                        + "two orientations."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("chosen-merge-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Forced-cut refutation in C2 times C4"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In G = ZMod 2 x ZMod 4 choose p=(0,1), q=(0,3), r=(1,0), "
                        + "s=(1,1), t=(1,3), a=(0,2), b=(1,2). For A={p,q,s,t,a,b} "
                        + "and the legal pair (a,b), the compressed alphabet is B={p,q,r,s,t}. "
                        + "The finite forced-cut proof shows that every Good B-order has r in "
                        + "position three and prefix sum b after two entries. Expanding r as a,b "
                        + "creates a proper final zero block of length three; expanding as b,a "
                        + "creates a proper initial zero block of length three. The displayed "
                        + "Good B-order supplies the guard premise. The model and forced-cut "
                        + "classification follow the supplied candidate derivation and completed "
                        + "finite native audit. That audit also checks that A itself has Good "
                        + "order (p,a,t,q,s,b), and that the alternate legal pair (q,s), with "
                        + "q+s=r, succeeds: the Good compressed order (p,a,t,r,b) expands in "
                        + "orientation (q,s) to that A-order. These positive scope facts are "
                        + "native-audit evidence, not additional Lean theorems of this module. "
                        + "Only the every-chosen-pair adjacent lifting route is refuted. The "
                        + "original arbitrary-abelian ordering target and its same-M, "
                        + "original-coordinate, coefficient-one formulation remain OPEN."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) => Describe.Lean(
        DescribeId.Create("chosen-merge-" + id), DeclarationHandle.Create(Prefix + declaration),
        H(title), StatementSource.FromAuthor(Disp(F.Id(declaration))),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
