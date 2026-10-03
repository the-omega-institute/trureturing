using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History;

internal sealed class WellFoundedLeafMassConservationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local conservation on a well-founded tree gives conservation at its leaves.",
        H("Well-Founded Leaf Mass Conservation"),
        Blocks(Describe.Lean(
            DescribeId.Create("well-founded-leaf-mass-conservation"),
            DeclarationHandle.Create("D5/S0/History/WellFoundedLeafMassConservation.result"),
            H("The unconditional leaf mass equals the root mass"),
            StatementSource.FromAuthor(Disp(Seq(
                Sum, Underscore, Grp(F.Id("l"), InMacro, Sp, F.Id("Leaf")), Sp,
                F.Id("m"), Open, F.Id("l"), Close, Eq,
                F.Id("m"), Open, F.Id("nil"), Close))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let E be a countable type and T a prefix-closed set of finite "
                    + "lists over E containing the empty list. Let m assign an extended nonnegative "
                    + "real mass to every list. Assume the relation in which k precedes h exactly "
                    + "when both belong to T and k = h ++ [a] for some letter a is well-founded. "
                    + "Thus children, not shorter prefixes, are induction predecessors. A leaf is "
                    + "a member h of T for which no h ++ [a] belongs to T. At each nonleaf in T, "
                    + "assume m(h) equals the unconditional sum over all letters of m(h ++ [a]) "
                    + "for children in T, with zero for other letters. Then the unconditional sum "
                    + "of m over the subtype of all leaves equals m of the empty list.")),
                Paragraph(Text("Inside the proof, well-founded induction establishes that the "
                    + "mass of all terminal descendants of each node equals its mass. A descendant "
                    + "is represented uniquely by its suffix after that node. For a leaf, prefix "
                    + "closure excludes every nonempty suffix, leaving a singleton contribution. "
                    + "For a nonleaf, splitting nonempty suffixes by their first letter partitions "
                    + "terminal descendants into child families. Prefix closure excludes families "
                    + "outside T. Reindexing unconditional sums, applying the child induction "
                    + "hypotheses, and using local conservation proves the invariant. At the empty "
                    + "list every leaf is a descendant.")),
                Paragraph(Text("No finite branching, common finite depth, finite expected length, "
                    + "finite root mass, or positivity assumption is required. Zero and infinite "
                    + "masses, an empty alphabet, a root that is itself a leaf, and countably many "
                    + "finite arms of unbounded lengths are included. Leaves satisfy no local "
                    + "conservation premise. The result is conditional on the stated tree and mass "
                    + "hypotheses and does not assert that any particular controller satisfies them. "
                    + "No originality claim is made."))),
            DescribeRole.Theorem))));
}
