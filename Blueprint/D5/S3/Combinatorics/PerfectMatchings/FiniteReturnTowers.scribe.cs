using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PerfectMatchings;

internal sealed class FiniteReturnTowersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PerfectMatchings/FiniteReturnTowers.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Constructive first-return towers recover all orbit lengths, including untouched and singleton cycles.",
        H("Weighted First-Return Towers"),
        Blocks(
            Paragraph(Text("Let X be any finite type, f a permutation, S a marked subset, and R actual first-return data. "
                + "The data contain a permutation H of S and positive lengths l(x), with f^l(x)(x)=H(x) "
                + "and no intermediate positive iterate in S. Put T_x(0)=0 and "
                + "T_x(n+1)=T_x(n)+l(H^n(x)). Untouched points are those in cycles disjoint from S. "
                + "The tower model is the disjoint union of those points with pairs (x,k), where x is marked and 0<=k<l(x). "
                + "Its explicit successor preserves the original step on untouched points, increments k below the roof, "
                + "and sends (x,l(x)-1) to (H(x),0).")),
            Describe.Lean(DescribeId.Create("temporal-split"),
                DeclarationHandle.Create(Prefix + "ReturnData.temporal_decomposition"),
                H("Each Time Has One Completed-Return Count and Offset"),
                StatementSource.FromAuthor(Context(All("x", V("S"), All("k", V("Natural"),
                    new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("p"),
                        Call("Product", V("Natural"), V("Natural")),
                        Both(Split(V("p")), All("t", Call("Product", V("Natural"), V("Natural")),
                            Imp(Split(V("t")), Equal(V("t"), V("p"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural time k there is exactly one pair (n,d) with k=T_x(n)+d and "
                    + "0<=d<l(H^n(x)); its position is f^k(x)=f^d(H^n(x)). "
                    + "Strict increase of cumulative return times makes the half-open return intervals disjoint. "
                    + "Thus n records the full elapsed history even after an induced cycle repeats. "
                    + "Uniqueness of this temporal pair and uniqueness of the spatial tower coordinate both hold."))),
                DescribeRole.Theorem),
            Node("tower", "Every Original Point Has One Tower Coordinate", "ReturnData.tower_decomposition",
                Context(Call("ConstructedTowerEquivalence", V("R"), V("f"))),
                "The encoding sends an untouched point to itself and (x,k) to f^k(x). "
                + "First-visit minimality proves that different segments cannot overlap. "
                + "A greedy decomposition of every natural iterate into complete return segments and one interior offset proves surjectivity. "
                + "The encoding intertwines the explicit tower successor with f. No orbit partition is assumed."),
            Node("period", "Least Period Is the Sum of Actual Segment Lengths", "ReturnData.least_period_sum",
                Context(All("x", V("S"), All("N", V("Natural"),
                    Imp(Call("LeastPositivePeriod", V("H"), V("x"), V("N")),
                        Call("LeastPositivePeriod", V("f"), V("x"), Call("T", V("x"), V("N"))))))),
                "The cumulative return time T_x(N) returns to x. If a shorter positive original time returned to x, "
                + "its greedy interior offset would have to be zero by first-visit minimality. "
                + "The remaining induced return count would contradict the least positive H-period. "
                + "This proves minimality, not just existence of a return."),
            Paragraph(Text("Write p_f(z) for the least positive f-period, including period one. "
                + "Write L(x)=sum_{i<p_H(x)} l(H^i(x)). The full cycle inventory is the rational polynomial "
                + "I_f(Z)=sum_z Z^p_f(z)/p_f(z). Each cycle contributes exactly one monomial, including fixed points. "
                + "This is an additive encoding of the complete cycle multiset, not the conventional multiplicative cycle-index polynomial.")),
            Node("inventory", "Every Additive Orbit-Length Statistic", "ReturnData.weighted_inventory",
                Context(All("A", V("AdditiveCommutativeMonoid"),
                    All("Phi", Call("Function", V("Natural"), V("A")),
                        Equal(Call("RootSum", V("f"), V("Phi")),
                            Call("Add", Call("UntouchedRootSum", V("R"), V("Phi")),
                                Call("WeightedEndpointSum", V("R"), V("Phi"))))))),
                "For every additive observable Phi, sum_z Phi(p_f(z)) equals the untouched-root sum "
                + "plus sum_x l(x) times Phi(L(x)). The constructive tower bijection supplies the change of variables, "
                + "and the least-period theorem supplies the weight of each tower. Taking length indicators recovers every root multiplicity."),
            Node("cycle-inventory", "The Complete Weighted Cycle Inventory", "ReturnData.weighted_cycle_inventory",
                Context(Equal(Call("CycleInventory", V("f")),
                    Call("Add", Call("UntouchedInventory", V("R")), Call("WeightedInventory", V("R"))))),
                "Apply the preceding inventory theorem to Phi(n)=Z^n/n over rational polynomials. "
                + "The marked contribution is sum_x l(x) Z^L(x)/L(x), and the untouched contribution remains explicit. "
                + "The reciprocal is always defined at a positive period. Empty marked sets and singleton original cycles remain in scope."))));

    private static DocumentBlock Node(string id, string title, string name, Formula formula, string proof) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(proof))), DescribeRole.Theorem);
    private static Formula Both(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Split(Formula p) => Both(
        Equal(V("k"), Add(Call("Elapsed", V("R"), V("x"), Call("First", p)), Call("Second", p))),
        Both(new Formula.Relation(Call("Second", p), FormulaRelationOperator.LessThan,
                Call("Length", V("R"), Call("NextIterate", V("R"), Call("First", p), V("x")))),
            Equal(Call("Iterate", V("f"), V("k"), V("x")),
                Call("Iterate", V("f"), Call("Second", p),
                    Call("NextIterate", V("R"), Call("First", p), V("x"))))));
    private static Formula V(string name) => F.Id(name);
    private static Formula All(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), domain, body);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Context(Formula body) => Disp(All("X", V("FiniteType"),
        All("f", Call("Perm", V("X")), All("S", Call("Set", V("X")),
            All("R", Call("FirstReturnData", V("f"), V("S")), body)))));
}
