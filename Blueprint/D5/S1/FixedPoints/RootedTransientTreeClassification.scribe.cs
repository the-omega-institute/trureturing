using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.FixedPoints;

internal sealed class RootedTransientTreeClassificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Recursive unordered branch codes classify finite transient rooted in-trees.",
        H("Rooted Transient-Tree Classification"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rooted-transient-tree-classification"),
                DeclarationHandle.Create(
                    "D5/S1/FixedPoints/RootedTransientTreeClassification."
                        + "rooted_transient_tree_classification"),
                H("Equal branch codes characterize rooted-tree isomorphism"),
                StatementSource.FromAuthor(ClassificationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let updateY and updateZ be self-maps of finite carriers. A child of a "
                            + "state is constructed as an actual predecessor under its update, "
                            + "with periodic predecessors excluded.")),
                    Paragraph(Text(
                        "A cycle in the resulting child relation would make its first state "
                            + "periodic. Finiteness therefore makes this relation well-founded, "
                            + "which supports recursion from leaves toward each chosen root.")),
                    Paragraph(Text(
                        "The branch code recursively forms the unordered multiset of all child "
                            + "codes and applies Mathlib's injective multiset encoding. Rooted "
                            + "isomorphism is defined independently by a one-to-one multiset "
                            + "matching whose paired children are recursively isomorphic.")),
                    Paragraph(Text(
                        "The forward direction maps every recursive child matching to equal child "
                            + "codes. Conversely, equality of the encoded multisets gives a "
                            + "one-to-one matching of equal child codes, and well-founded induction "
                            + "turns every matched pair into a subtree isomorphism.")),
                    Paragraph(Text(
                        "Repository and pinned-library searches found no existing unordered "
                            + "finite-tree classifier. The proof directly reuses periodic points, "
                            + "finite acyclic well-foundedness, multiset relational matching, and "
                            + "the injectivity of the pinned multiset encoding."))),
                DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments) =>
        Call(name, arguments);

    private static Formula Typeclass(string name, Formula carrier) =>
        Seq(OpenBracket, Apply(name, carrier), CloseBracket);

    private static Formula ClassificationFormula()
    {
        Formula carrierY = F.Id("Y");
        Formula carrierZ = F.Id("Z");
        Formula updateY = F.Id("updateY");
        Formula updateZ = F.Id("updateZ");
        Formula rootY = F.Id("y");
        Formula rootZ = F.Id("z");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));

        return Disp(Seq(
            Forall, Sp, carrierY, Comma, Sp, carrierZ, Colon, Sp, type, Comma, RowBreak, Grp(),
            Typeclass("Fintype", carrierY), Comma, Sp,
            Typeclass("Fintype", carrierZ), Comma, RowBreak, Grp(),
            updateY, Colon, Sp, carrierY, Sp, To, Sp, carrierY, Comma, Sp,
            updateZ, Colon, Sp, carrierZ, Sp, To, Sp, carrierZ, Comma, RowBreak, Grp(),
            rootY, Colon, Sp, carrierY, Comma, Sp, rootZ, Colon, Sp, carrierZ, Comma, RowBreak,
            Grp(),
            Apply("RootedTransientTreeIsomorphic", updateY, updateZ, rootY, rootZ), Sp,
            Iff, Sp,
            Apply("branchCode", updateY, rootY), Sp, Eq, Sp,
            Apply("branchCode", updateZ, rootZ), Dot));
    }
}
