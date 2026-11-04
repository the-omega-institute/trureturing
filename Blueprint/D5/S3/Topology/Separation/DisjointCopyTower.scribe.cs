using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Separation;

internal sealed class DisjointCopyTowerDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/Separation/DisjointCopyTower.";

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Statement()
    {
        Formula x = F.Id("X"), k = F.Id("K"), a = F.Id("A"), b = F.Id("B");
        Formula sets = Call("Set", x);
        Formula conclusion = Exists("A", sets, Exists("B", sets,
            And(Call("IsClosed", a), And(Call("IsClosed", b),
                And(Call("Infinite", a), And(Call("Infinite", b),
                    And(Call("Disjoint", a, b),
                        Call("Nonempty", Call("Homeomorph", Call("Subtype", a), Call("Subtype", b))))))))));
        Formula hypotheses = And(Call("AllLevelsCompact", k),
            And(Call("AllLevelsNonempty", k), Call("DisjointSuccessorCopies", k)));
        return Disp(All("X", F.Id("TopologicalSpaceU"),
            Imp(Call("T2Space", x), All("K", Call("Function", F.Id("Nat"), sets),
                Imp(hypotheses, conclusion)))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A tower of nonempty compact sets with two disjoint copies at every step forces disjoint infinite closed homeomorphic subspaces.",
        H("Disjoint compact copy towers"),
        Blocks(
            Paragraph(Text(
                "X is any Hausdorff space; no compactness of X is assumed. K is a sequence of subsets of X. "
                + "AllLevelsCompact means that every K(n) is compact, and AllLevelsNonempty means that every K(n) contains a point. "
                + "DisjointSuccessorCopies means: for every natural n there are ambient subsets A and B contained in K(n), "
                + "disjoint in X, and homeomorphisms from K(n+1) onto A and B with their actual subtype topologies. "
                + "No infinitude of the levels or closedness of the copies is supplied as an assumption.")),
            Describe.Lean(
                DescribeId.Create("disjoint-infinite-closed-copies"),
                DeclarationHandle.Create(Owner + "exists_disjoint_infinite_closed_copies"),
                H("A compact binary-copy tower contains two infinite closed copies"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Topology/kania2026talagrand")),
                Blocks(
                    Paragraph(Text(
                        "Suppose some level is finite. Among the finite cardinalities of all finite levels choose the least one, attained at K(j). "
                        + "The first copy gives an injection from K(j+1) into the finite set K(j), hence the next level is finite as well. "
                        + "Nonemptiness of K(j+1) supplies a point in the second copy. Disjointness puts that point outside the first injection's range. "
                        + "Fintype.card_lt_of_injective_of_notMem therefore gives a strictly smaller finite level cardinality, contradicting minimality. "
                        + "This proves that every level is infinite; it does not infer infinitude from nonemptiness alone.")),
                    Paragraph(Text(
                        "Take the two copies of K(1) inside K(0). They are compact because the respective homeomorphisms are continuous, "
                        + "and therefore closed in the Hausdorff ambient space. Their underlying bijections transfer the established infinitude of K(1). "
                        + "The inverse of the first homeomorphism followed by the second gives a homeomorphism between these disjoint infinite closed sets.")),
                    Paragraph(Text(
                        "Consequently a Hausdorff space with no two disjoint infinite closed homeomorphic subspaces has no such tower. "
                        + "The tower is the 2DCP configuration in section 1 of arXiv:2607.06808v2."))),
                DescribeRole.Theorem))));
}
