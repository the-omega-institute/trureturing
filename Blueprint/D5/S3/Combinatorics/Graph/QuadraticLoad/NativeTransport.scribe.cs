using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.QuadraticLoad;

internal sealed class NativeTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/QuadraticLoad/NativeTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The native finite-graph quadratic-load infimum respects injective graph maps and is additive on Cartesian products.",
        H("Transport of native quadratic allocations"),
        Blocks(
            Paragraph(Text(
                "Let G and H be finite simple graphs on nonempty vertex types V and W. "
                + "A feasible allocation a assigns a real number in [0,1] to every ordered pair, "
                + "with a(v,w)+a(w,v)=1 on edges. Its native load at v is the sum of a(v,w)^2 "
                + "over neighbours w. The function maxLoad is the maximum of those loads, and "
                + "kappa is the infimum of maxLoad over all feasible allocations. "
                + "Nonedge coordinates remain bounded and never enter the load. "
                + "The Cartesian graph has vertices (v,w); an edge changes exactly one coordinate "
                + "along an edge of its factor, leaving the other coordinate fixed.")),
            Describe.Lean(DescribeId.Create("injective-native-transport"),
                DeclarationHandle.Create(Prefix + "kappa_le_of_injective_hom"),
                H("Restriction along an injective graph map"),
                StatementSource.FromAuthor(InjectionFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Take an actual minimizing allocation a on H. Pull it back by f: the share "
                    + "at (v,v') is a(f(v),f(v')). All share bounds and edge-complement equations "
                    + "are preserved. Injectivity makes the images of the neighbours of v distinct; "
                    + "edge preservation places all of them among the neighbours of f(v). "
                    + "The pulled-back load is consequently at most the ambient load because "
                    + "the additional ambient summands are nonnegative squares. Taking the "
                    + "maximum and using the native minimizing allocation proves the inequality. "
                    + "The map need not be surjective or reflect adjacency."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-cartesian-additivity"),
                DeclarationHandle.Create(Prefix + "kappa_box"),
                H("Cartesian additivity on the full allocation domain"),
                StatementSource.FromAuthor(BoxFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For the upper bound take actual factor minimizers a and b. At an ordered "
                        + "pair x,y in V times W use b(x.second,y.second) when x.first=y.first, "
                        + "and a(x.first,y.first) otherwise. This is feasible even off edges. "
                        + "The two disjoint neighbour classes give exactly the sum of the factor loads.")),
                    Paragraph(Text(
                        "For the lower bound use the full simplex of nonnegative vectors of total "
                        + "mass one. On actual feasible allocations the payoff is the weighted sum "
                        + "of native loads. The allocation domain is compact and convex; the simplex "
                        + "is nonempty, compact and convex. The payoff is continuous, convex in "
                        + "allocation, and affine in the law. Pinned Sion supplies a saddle point. "
                        + "Testing every point mass shows that its law p bounds kappa(G) below the "
                        + "p-weighted load for every feasible allocation; the same argument gives q for H.")),
                    Paragraph(Text(
                        "Fix one ambient product allocation A. Every slice at fixed w is feasible "
                        + "on G, and every slice at fixed v is feasible on H. Apply the two universal "
                        + "factor certificates, multiply by q(w) and p(v), respectively, then sum. "
                        + "Under the one common law p(v)q(w), the disjoint neighbour classes combine "
                        + "to the ambient load. Normalization bounds its expectation by maxLoad(A). "
                        + "Choosing an actual ambient minimizer gives the lower inequality. "
                        + "All feasible allocations are retained, and zero masses are allowed: "
                        + "the argument never divides by a law coordinate. It includes singletons, "
                        + "edgeless factors and unequal vertex-type universes. "
                        + "These two graph results do not establish legal-word block correspondences "
                        + "or the existence and characterization of a legal-word growth constant."))),
                DescribeRole.Theorem))));

    private static Formula Call(string n, params Formula[] a) =>
        new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(n)), [.. a]);
    private static Formula All(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Instance(Formula t, Formula b) => Seq(OpenBracket, t, CloseBracket, Sp, b);

    private static Formula Graphs(Formula body)
    {
        Formula v = F.Id("V"), w = F.Id("W"), g = F.Id("G"), h = F.Id("H");
        return All("V", F.Id("Type"), All("W", F.Id("Type"),
            Instance(Call("Fintype", v), Instance(Call("Fintype", w),
            Instance(Call("Nonempty", v), Instance(Call("Nonempty", w),
            All("G", Call("SimpleGraph", v), All("H", Call("SimpleGraph", w),
            Instance(Call("DecidableRel", Call("Adj", g)),
            Instance(Call("DecidableRel", Call("Adj", h)), body))))))))));
    }

    private static Formula InjectionFormula()
    {
        Formula v = F.Id("V"), w = F.Id("W"), g = F.Id("G"), h = F.Id("H");
        Formula f = F.Id("f"), x = F.Id("x"), y = F.Id("y");
        Formula edges = All("x", v, All("y", v,
            Imp(Call("Adj", g, x, y), Call("Adj", h, Call("f", x), Call("f", y)))));
        Formula result = new Formula.Relation(Call("kappa", g), FormulaRelationOperator.LessThanOrEqual, Call("kappa", h));
        return Disp(Graphs(All("f", new Formula.TypeArrow(v, w), Imp(Call("Injective", f), Imp(edges, result)))));
    }

    private static Formula BoxFormula()
    {
        Formula g = F.Id("G"), h = F.Id("H");
        return Disp(Graphs(new Formula.Relation(Call("kappa", Call("boxProd", g, h)),
            FormulaRelationOperator.Equal, new Formula.Binary(Call("kappa", g),
                FormulaBinaryOperator.Add, Call("kappa", h)))));
    }
}
