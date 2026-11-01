using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class CubicPowerClassificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All admissible parameters, all positive faithful powers, five native graph types and exact component multipliers.", H("Complete well-covered-power classification of cubic circulants"), Blocks(
            Paragraph(Text("Throughout, n is even and at least four, and 1 at most a is less than n/2. Let G=cubic(n,a), h=gcd(n,a), ell=n/h and g=gcd(a,n/2). The allowed set is exactly {3,4,5,6,8}. AllPowers(G) means that every faithful finite-distance power with positive exponent is well-covered. The component size function s(ell,d) has first values: ell=4 gives 1; ell=6 or 8 gives 3,1; ell=3 gives 2,1; ell=5 gives 4,2,1. Every later value is one. The five named types are K4=C4(1,2), K3,3=C6(1,3), P3=C6(2,3), M8=C8(1,4), and P5=C10(2,5). Their diameters are 1,2,2,2,3. The first-power classification is attributed to Brown and Hoshino, Well-covered circulant graphs, DOI 10.1016/j.disc.2010.11.007; the component decomposition is further attributed to Davis, Domke and Garner. Fresh verification recovered Brown-Hoshino metadata but not the full primary mathematical text, so the precise historical theorem-text attribution remains ASSUMED-UNVERIFIED. No novelty claim is made for that classification.")),
            Node("all_powers_iff", "Every positive power exactly when the first is well-covered",
                And(Iff(C("AllPowers",I("G")),C("WellCovered",I("G"))),Iff(C("WellCovered",I("G")),C("mem",I("ell"),C("fiveOrders")))),
                "The native first-power spectra classify all Mobius and prism components. Their exact attained values show that only ell in the stated set can be well-covered. Conversely, all their powers have singleton spectra: diameter bounds make later powers complete, and the pentagonal square is handled by its actual complement ten-cycle. The faithful component transport proves the equivalence for the entire disconnected graph."),
            Node("cubic_power_spectrum", "Exact uniform sizes and attainability in every component multiplicity",
                Imp(C("mem",I("ell"),C("fiveOrders")),All("d",C("Nat"),Imp(Le(D(1),I("d")),Eq(C("spectrum",C("graphPower",I("G"),I("d"))),C("singleton",C("mul",I("g"),C("componentPowerSize",I("ell"),I("d")))))))),
                "Each actual component has the singleton spectrum s(ell,d). The full componentwise Minkowski formula gives exactly g times that value, including an actual maximal independent Finset attaining the sum. This is a consequence of native component isomorphisms and finite-path powers, rather than a scalar decomposition assumption."),
            Node("native_type_table", "The native five-type table",
                All("t",C("ConnectedType"),And(C("GraphIso",C("cubic",C("typeOrder",I("t")),C("typeStep",I("t"))),C("typeGraph",I("t"))),And(C("Connected",C("cubic",C("typeOrder",I("t")),C("typeStep",I("t")))),And(Eq(C("diam",C("cubic",C("typeOrder",I("t")),C("typeStep",I("t")))),C("typeDiameter",I("t"))),All("d",C("Nat"),Imp(Le(D(1),I("d")),Eq(C("spectrum",C("graphPower",C("cubic",C("typeOrder",I("t")),C("typeStep",I("t"))),I("d"))),C("singleton",C("typePowerSize",I("t"),I("d")))))))))),
                "The index t ranges over exactly the five types listed above. The graph side of the correspondence is literal: the complete graph, complete bipartite graph, two Cartesian prisms and the native eight-vertex Mobius graph. Parity coordinates identify the six-vertex Mobius graph with K3,3. The odd-order component construction identifies each listed prism circulant. All exponent statements quantify over every positive natural number."),
            Node("classified_component_type", "Every actual component belongs to the native table",
                Imp(C("mem",I("ell"),C("fiveOrders")),All("C",C("Components",I("G")),Ex("t",C("ConnectedType"),And(Eq(I("ell"),C("NatDiv",C("typeOrder",I("t")),C("gcd",C("typeOrder",I("t")),C("typeStep",I("t"))))),C("GraphIso",C("componentGraph",I("C")),C("typeGraph",I("t"))))))),
                "The all-parameter component decomposition selects the even Mobius or odd prism case. The attained first-power spectrum restricts it to the appropriate entry of the five-type table. The theorem supplies a graph isomorphism on each actual component support and also identifies its normalized cycle order."),
            Node("eventual_spectrum", "Exactly one selected vertex per original component",
                Imp(C("mem",I("ell"),C("fiveOrders")),All("d",C("Nat"),Imp(Le(D(3),I("d")),Eq(C("spectrum",C("graphPower",I("G"),I("d"))),C("singleton",I("g")))))),
                "By exponent three all five connected models are complete. Each maximal independent set therefore has exactly one vertex from each original component. Positive faithful powers preserve those components, so the exact eventual cardinality is g, with attainment.")), []));
    private static DocumentBlock Node(string name, string title, Formula statement, string explanation) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/CubicPowerClassification." + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))),
            name is "mobiusIso" or "pentagon_square_complement_iso" ? DescribeRole.Definition : DescribeRole.Theorem);
    private static Formula I(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] a) => a.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(s))
        : new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. a]);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Ex(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
}
