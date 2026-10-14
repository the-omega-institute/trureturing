using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeCoreSplicingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeCoreSplicing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual native circle complements and literal c edges construct a Hamilton cycle on the complete two-star T core union.",
        H("Splicing the Complete Native T Core"),
        Blocks(
            Paragraph(Text(
                "For m at least four, configurations are the actual permutations of Fin(m+1). "
                + "The generators a, b and c reverse the first m+1, m and m-1 positions. "
                + "Let tau exchange position zero with the last position. CoreDomain(m) is the union "
                + "of the two insertion stars supplied by a*c and tau*a*c. Each star is specified "
                + "by deleting its last label from the actual oriented tuple circle, allowing whole "
                + "reversal. The graph coreGraph(m) is the full three-generator Cayley graph induced "
                + "on this independently specified union. CoreDeletedEdge(m) is the literal set "
                + "of old T cuts: one a edge at each core and one b edge at each noncore port. "
                + "It is specified from those actual ports before any paths or cycle are chosen.")),
            Describe.Lean(DescribeId.Create("native-core-hamiltonian-cycle"),
                DeclarationHandle.Create(Prefix + "native_core_hamiltonian_cycle"),
                H("One Actual Hamilton Cycle Covers the Whole Core Union"),
                StatementSource.FromAuthor(CycleFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There is a core vertex z whose actual configuration is the identity and a "
                        + "genuine coreGraph(m) Hamilton cycle w based at z. Every core vertex occurs "
                        + "exactly once before the return. The first edge of w joins z to a vertex "
                        + "whose configuration is exactly c(m), so the closing connection is a literal "
                        + "generator edge, rather than an endpoint pairing assumption. Every native "
                        + "a or b edge between core vertices is retained in the actual cycle whenever "
                        + "its underlying configuration edge is outside CoreDeletedEdge(m).")),
                    Paragraph(Text(
                        "The earned circle partition has Fin(m) plus Fin(m-2) owners. In T order, "
                        + "take the identity core, all lower noncore gaps, the tau core and all upper "
                        + "noncore gaps. At the two cores use the actual a-edge complements; at every "
                        + "other circle use the actual b-edge complement. Each complement is a path "
                        + "of length 2(m+1)-1 that exhausts its complete independent circle domain. "
                        + "Lift these paths to the induced graph. Unique ownership makes their full "
                        + "supports disjoint, and full ownership makes every core vertex occur once.")),
                    Paragraph(Text(
                        "The noncore seam identity is a*c*(b*c)^j*b*c = a*c*(b*c)^(j+1). "
                        + "The native halfword identity a*c*(b*c)^(m-2)=tau connects the lower half "
                        + "to the second a complement and makes the upper half return to identity. "
                        + "The complete cut list is therefore a closed chain of actual c connections. "
                        + "PathRingSplicing joins the full paths and returns their closing edge first; "
                        + "multiplying the final seam by the involution c identifies its endpoint as c. "
                        + "The complete native-complement edge inventory earns every other a/b edge "
                        + "in its owned circle. The induced-walk edge map and injective subtype map "
                        + "preserve that membership. Each piece edge occurs in the literal chainEdges "
                        + "list and therefore in the final reversed cycle edge list. This proves the "
                        + "retained-edge assertion on the same actual Hamilton cycle."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "This theorem constructs the entire initial two-star core for every m at least four. "
                + "It does not yet cover the remaining insertion stars of the full second layer, "
                + "prove their complete actual contact classification, or establish the "
                + "higher simultaneous boundary induction. Those are separate remaining obligations "
                + "for all-size three-prefix-reversal Hamiltonicity.")))));

    private static Formula CycleFormula()
    {
        Formula m = F.Id("m"), z = F.Id("z"), w = F.Id("w"), y = F.Id("y");
        Formula vertices = Call("CoreVertices", m);
        Formula firstEdge = Some("y", vertices,
            And(Eq(Call("val", y), Call("c", m)),
                Eq(Call("headOption", Call("edges", w)), Call("some", Call("Sym2", z, y)))));
        Formula x = F.Id("x"), g = F.Id("g");
        Formula nativeGenerator = new Formula.Logic(Eq(g, Call("a", m)),
            FormulaLogicOperator.Or, Eq(g, Call("b", m)));
        Formula rawEdge = Call("Sym2", Call("val", x), Call("val", y));
        Formula hypotheses = And(nativeGenerator,
            And(Eq(Call("val", y), Call("rightMultiply", Call("val", x), g)),
                new Formula.Not(Call("CoreDeletedEdge", m, rawEdge))));
        Formula retained = All("x", vertices, All("y", vertices,
            All("g", Call("Configuration", m),
                Implies(hypotheses, Call("mem", Call("Sym2", x, y), Call("edges", w))))));
        Formula cycle = Some("w", Call("Walk", Call("coreGraph", m), z, z),
            And(Call("IsHamiltonianCycle", w), And(firstEdge, retained)));
        return Disp(All("m", Call("Nat"), Implies(Le(D(4), m),
            Some("z", vertices, And(Eq(Call("val", z), D(1)), cycle)))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
