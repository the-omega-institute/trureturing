using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Routing;

internal sealed class HannRouterProfilesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Routing/HannRouterProfiles.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Active literal router profiles distinguish every loaded address exactly when all deepest routers are active.",
        H("Physical router profiles"),
        Blocks(
            Def("internal-router-coordinates", "Router", "Internal router coordinates",
                "Router zero is empty. At a successor, none denotes the root router and some(b,v) "
                + "denotes v in the right child when b is true and the left child otherwise. "
                + "routerLabel reads the router field of the actual nested Tree. Incident and output "
                + "rails are excluded. This indexes every internal router, including those off the programmed path."),
            Def("deepest-router", "deepest", "Deepest physical router",
                "snoc appends a final bit to the existing head-first Address. deepest n u is the actual "
                + "depth-n router reached by the length-n prefix u. In the fully programmed tree for snoc u b, "
                + "its label at deepest n i is encode b if i equals u and wait otherwise. Siblings snoc u false "
                + "and snoc u true agree at every other internal router. Both statements hold at every natural n."),
            Def("loaded-router-label", "loadedLabel", "Actual sequential loading",
                "loadedLabel reads routerLabel after load n n on loading n a bus zero. The existing "
                + "sequential-loading identity identifies this tree with programmed n a n, for every external "
                + "qutrit bus label. Thus no bus label affects the observed router profile."),
            Def("active-profile", "SameProfile", "Active profile equality",
                "A rate q is an arbitrary function on all internal routers. A router is active precisely "
                + "when its rate is less than one. SameProfile requires equality of loadedLabel at every "
                + "active router, allowing the two bus labels to differ. Separates means that this equality "
                + "always forces the two addresses to coincide."),
            Describe.Lean(DescribeId.Create("deepest-activity-characterizes-separation"),
                DeclarationHandle.Create(Module + "profile_separation_iff"),
                H("Exact physical profile separation criterion"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive tree depth n+1, all addresses are distinguished exactly when "
                    + "every depth-n router has rate less than one. Necessity uses two siblings under an "
                    + "inactive deepest router: every other literal router label agrees. Sufficiency "
                    + "observes the deepest router under the first address prefix. Different prefixes "
                    + "give an occupied label versus wait; equal prefixes give the two encoded final bits. "
                    + "No restriction on the real rates is needed for this combinatorial equivalence, so "
                    + "independent rates in the closed unit interval and both endpoints are included. "
                    + "The statement concerns the actual loaded physical coordinates. It does not assert "
                    + "record independence, Gram rank or kernel, simplex optimization, or a noisy-continuation formula."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Def(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    private static Formula I(string x) => F.Id(x);
    private static Formula C(string x, params Formula[] a) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(x), [.. a]);
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    private static Formula All(string x, Formula t, Formula b) => new Formula.BindMany(
        FormulaQuantifier.ForAll, [new(FormulaIdentifier.Create(x), t)], b);
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);

    private static Formula Statement()
    {
        Formula n = I("n"), q = I("q"), a = I("a"), ap = I("aPrime"),
            bus = I("bus"), bp = I("busPrime"), v = I("v"), u = I("u");
        Formula depth = new Formula.Binary(n, FormulaBinaryOperator.Add, D(1)),
            routers = C("Router", depth), addresses = C("Address", depth);
        var same = All("v", routers, Imp(Lt(App(q, v), D(1)), Eq(
            C("loadedLabel", depth, a, bus, v), C("loadedLabel", depth, ap, bp, v))));
        var separates = All("a", addresses, All("aPrime", addresses,
            All("bus", I("Qutrit"), All("busPrime", I("Qutrit"), Imp(same, Eq(a, ap))))));
        var deepestActive = All("u", C("Address", n), Lt(App(q, C("deepest", n, u)), D(1)));
        return All("n", I("Nat"), All("q", Arr(routers, I("Real")),
            new Formula.Logic(separates, FormulaLogicOperator.Iff, deepestActive)));
    }
}
