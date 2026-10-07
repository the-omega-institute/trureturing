using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class PairSelectionReroutingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PairSelectionRerouting.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "If each support has at least two vertices and every legal pair selection is sparse, some selection has only two-element supports on its four-cliques.",
        H("Rerouting Pair Selections"),
        Blocks(
            Paragraph(Text(
                "Let I and V be finite types, and let R(i) be a finite set of vertices for every "
                + "owner i in I. A legal selection e chooses a two-element subset e(i) of R(i). "
                + "Different owners may select the same pair. Sparse(e) means that for every "
                + "vertex set S, twice the number of owners with e(i) contained in S is at most "
                + "three times the cardinality of S. Thus parallel edges are counted with their "
                + "owner multiplicities. Cliques(e) is the family of four-element vertex sets C "
                + "whose six unordered pairs all occur among the selected pairs; each such C "
                + "is counted once.")),
            Describe.Lean(DescribeId.Create("minimum-rigidity"),
                DeclarationHandle.Create(Prefix + "minimal_selection_rigid"),
                H("A Minimum Selection Has Only Rigid Four-Cliques"),
                StatementSource.FromAuthor(MinimumFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume every legal selection is sparse, and e minimizes the number of "
                    + "four-cliques among legal selections. For each C in Cliques(e), every "
                    + "owner i with e(i) contained in C has exactly two vertices in R(i). "
                    + "The hypothesis concerns all selections, so it also supplies sparsity "
                    + "after changing one owner's pair.")),
                    Paragraph(Text(
                        "A four-clique already uses six indexed owners on four vertices. "
                        + "Sparsity therefore makes every one of its six pairs have a unique "
                        + "owner. If an owner of uv has a third available vertex w, replace uv "
                        + "by uw. This destroys the old four-clique. When w lies inside it, "
                        + "the new simple edge was already present, so no clique is created. "
                        + "When w lies outside it, a newly created four-clique must contain uw. "
                        + "Its intersection with the old four vertices has size t equal to "
                        + "one, two, or three. Together with the five surviving old pairs, "
                        + "it gives at least 11 minus binomial(t,2) distinct edges on 8 minus t "
                        + "vertices. Each of the three cases violates sparsity. The rerouting "
                        + "therefore strictly reduces the clique family, contradicting minimality."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rigid-selection"),
                DeclarationHandle.Create(Prefix + "exists_rigid_selection"),
                H("Existence of a Rigid Selection"),
                StatementSource.FromAuthor(ExistenceFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If each support has at least two vertices and every legal selection is "
                    + "sparse, a legal selection exists in which each owner on any four-clique "
                    + "has a two-element support. Choose a selection with the minimum clique "
                    + "count from the nonempty finite family of legal selections, and apply "
                    + "the preceding theorem. In particular, if all supports have at least "
                    + "three vertices, this selection has no four-clique. The conclusion is "
                    + "about pair selection and does not assert a coloring. Empty owner and "
                    + "vertex types are included whenever the stated hypotheses hold."))),
                DescribeRole.Theorem))));

    private static Formula MinimumFormula() => Disp(All("R", Call("Supports"),
        All("e", Call("Selections"),
            Implies(And(Call("Selects", F.Id("R"), F.Id("e")),
                And(Call("EverySelectionSparse", F.Id("R")),
                    Call("MinimumCliqueCount", F.Id("R"), F.Id("e")))),
                Call("RigidCliqueOwners", F.Id("R"), F.Id("e"))))));

    private static Formula ExistenceFormula() => Disp(All("R", Call("Supports"),
        Implies(And(Call("SupportsAtLeastTwo", F.Id("R")),
            Call("EverySelectionSparse", F.Id("R"))),
            new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("e"), Call("Selections"),
                And(Call("Selects", F.Id("R"), F.Id("e")),
                    Call("RigidCliqueOwners", F.Id("R"), F.Id("e")))))));

    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula And(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.And, r);
    private static Formula Implies(Formula l, Formula r) =>
        new Formula.Logic(Seq(Open, l, Close), FormulaLogicOperator.Implies, Seq(Open, r, Close));
}
