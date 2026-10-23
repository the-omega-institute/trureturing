using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeCircleComplementDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleComplement.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A native a/b circle has complete actual cut complements, with supports exhausting its independently defined rotation-and-reversal domain.",
        H("Complete Native Circle Cut Pieces"),
        Blocks(
            CoordinateAPI("native_configurationCycle_rotation", "Actual Rotation Preserves the Tuple Cycle", "Right multiplication by any finCycle rotation preserves the actual tuple modulo rotations.", false),
            CoordinateAPI("native_configurationCycle_reversal", "Actual Full Reversal Reverses the Tuple Cycle", "Right multiplication by a reverses the actual configuration tuple cycle.", false),
            Paragraph(Text(
                "Let m be at least three and let z be a permutation of Fin(m+1). Circle(z,v) means that the "
                + "actual circular tuple of v equals that of z or its whole reversal; only rotations are "
                + "quotiented in the tuple. Thus Circle is specified without reference to a walk. Its coordinates "
                + "are z*R^r and z*R^r*a for r in Fin(m+1), where R=ab rotates all positions by one.")),
            Describe.Lean(DescribeId.Create("circle-equivalence"), DeclarationHandle.Create(Prefix + "circleEquiv"),
                H("All Actual Native Circle Coordinates"), StatementSource.FromAuthor(EquivFormula()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The coordinates form a bijection onto Circle(z). Injectivity reuses the existing deletion-star "
                    + "coordinateEquiv at one fixed gap, rather than proving a second dihedral injection. "
                    + "Surjectivity comes from actual tuple rotations; the negative case applies a whole reversal "
                    + "first, and then uses the involution a to recover the configuration."))), DescribeRole.Definition),
            Complement("b-complement", "native_b_complement", "The Complete b-Cut Complement", false,
                "The literal H word is U_m=(ab)^m*a, with length 2(m+1)-1 and product b. Its scanl is the "
                + "ordered flattened list [z*R^r,z*R^r*a] over all r in Fin(m+1). The circle-coordinate bijection "
                + "makes this trace simple and exhaustive. Every step is an actual a/b edge. A simple path "
                + "containing the edge between its endpoints would have length one, so the displayed long path "
                + "avoids its b-cut edge and transfers to the graph with that edge deleted."),
            Complement("a-complement", "native_a_complement", "The Complete a-Cut Complement", true,
                "Start with the actual b-cut H path. Its second vertex is z*a. Reverse the path after its first "
                + "a-edge, and prepend the actual b-edge from z to z*b. The support is z followed by the reverse "
                + "of the H trace's tail. It is a permutation of the original complete simple support. Its endpoint "
                + "is z*a, its length remains 2(m+1)-1, and simplicity again excludes the a-cut edge."),
            Describe.Lean(DescribeId.Create("complement-edge-inventory"),
                DeclarationHandle.Create(Prefix + "native_complement_edge_inventory"),
                H("Every Other Native Edge Is Retained"),
                StatementSource.FromAuthor(InventoryFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let g be a or b, and let w be an actual a/b path from z to z*g, of length "
                    + "2(m+1)-1, whose support is exactly Circle(z). At every x in Circle(z), "
                    + "and for either h=a or h=b, the edge from x to x*h occurs in w exactly when "
                    + "it differs from the deleted endpoint edge from z to z*g. To prove this, "
                    + "close the actual path with that endpoint edge. Every supported vertex has "
                    + "two cycle neighbors, and the native a/b graph allows only x*a and x*b. "
                    + "These are distinct, so equality of the finite neighbor cardinalities "
                    + "forces both actual edges into the cycle. Removing its literal first edge "
                    + "leaves precisely all other native edges in the complement. This earns the "
                    + "retained b edges required at subsequent one-contact insertion suppliers."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complement-full-edge-inventory"),
                DeclarationHandle.Create(Prefix + "native_complement_full_edge_inventory"),
                H("The Complete Complement Edge Set"),
                StatementSource.FromAuthor(FullInventoryFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any actual undirected configuration edge e, membership in the complete "
                    + "native complement is equivalent to NativeCircleEdge(z,e) and inequality "
                    + "with the literal cut. NativeCircleEdge means that e joins x to x*h for "
                    + "an actual x in Circle(z) and h equal to a or b. The forward direction uses "
                    + "the actual walk adjacency and support to earn that form; the complete "
                    + "native retained-edge theorem supplies both cut exclusion and the converse. "
                    + "This arbitrary-edge equivalence is consumed by the full T/E graft surgery "
                    + "inventory, including its absence direction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-circle-edge-endpoint"),
                DeclarationHandle.Create(Prefix + "native_circle_edge_endpoint"),
                H("Both Native Edge Endpoints Remain in Their Actual Circle"),
                StatementSource.FromAuthor(EndpointFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every m, if e is a NativeCircleEdge(z,e), each actual configuration v "
                    + "belonging to the undirected edge e lies in Circle(z). The native generators "
                    + "a and b both reverse the actual tuple cycle: b is a whole reversal followed "
                    + "by an oriented rotation. Circle is closed under either action. Undirected "
                    + "edge membership selects one of these two actual endpoints. Complete T "
                    + "deleted-edge classification consumes this endpoint property to identify "
                    + "the unique circle owner of any alleged retained old cut."))), DescribeRole.Theorem),
            Paragraph(Text(
                "These are complete native D-circle pieces for switching constructions. Their membership "
                + "equivalences cover every configuration in the independent circle domain, with no finite search. "
                + "Connecting multiple circles still requires actual connecting edges, distinct circle ownership "
                + "and complete coverage of the intended larger domain.")))));

    private static Formula CoordinateFormula(string selector)
    {
        Formula m = F.Id("m"), z = F.Id("z"), r = F.Id("r");
        Formula cycle(Formula v) => Call("configurationCycle", v);
        Formula body = selector switch
        {
            "native_configurationCycle_rotation" => All("r", Call("Fin", Add(m, D(1))),
                Eq(cycle(Mul(z, Call("finCycle", r))), cycle(z))),
            "native_configurationCycle_reversal" => Eq(cycle(Mul(z, Call("a", m))), Call("reverse", cycle(z))),
            _ => throw new System.ArgumentOutOfRangeException(nameof(selector))
        };
        return Disp(All("m", Call("Nat"), All("z", Call("Configuration", m), body)));
    }

    private static DocumentBlock CoordinateAPI(string selector, string title, string meaning, bool definition) =>
        Describe.Lean(DescribeId.Create(selector.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + selector), H(title), StatementSource.FromAuthor(CoordinateFormula(selector)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(meaning))),
            definition ? DescribeRole.Definition : DescribeRole.Theorem);

    private static DocumentBlock Complement(string id, string name, string title, bool aCut, string proof) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(ComplementFormula(aCut)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(proof))), DescribeRole.Theorem);

    private static Formula EquivFormula()
    {
        Formula m = F.Id("m"), z = F.Id("z");
        Formula domain = Call("Prod", Call("Fin", Add(m, D(1))), Call("Bool"));
        return Disp(All("m", Call("Nat"), Implies(Le(D(3), m),
            All("z", Call("Configuration", m), Call("Equiv", domain, Call("CircleDomain", z))))));
    }

    private static Formula EndpointFormula()
    {
        Formula m = F.Id("m"), z = F.Id("z"), v = F.Id("v"), e = F.Id("e");
        return Disp(All("m", Call("Nat"), All("z", Call("Configuration", m),
            All("v", Call("Configuration", m), All("e", Call("Sym2Type", Call("Configuration", m)),
                Implies(And(Call("NativeCircleEdge", z, e), Call("mem", v, e)),
                    Call("Circle", z, v)))))));
    }

    private static Formula ComplementFormula(bool aCut)
    {
        Formula m = F.Id("m"), z = F.Id("z"), w = F.Id("w"), v = F.Id("v");
        Formula endpoint = Call("rightMultiply", z, Call(aCut ? "a" : "b", m));
        Formula g = Call("deleteEdges", Call("nativeABGraph", m), Call("singletonEdge", z, endpoint));
        Formula trace = Call("scanl", Call("rightMultiply"), z, Call("uWord", m, m));
        Formula support = aCut ? Call("cons", z, Call("reverse", Call("tail", trace))) : trace;
        Formula full = All("v", Call("Configuration", m),
            new Formula.Logic(Call("mem", v, Call("support", w)), FormulaLogicOperator.Iff, Call("Circle", z, v)));
        Formula conclusion = Some("w", Call("Walk", g, z, endpoint),
            And(Call("IsPath", w), And(Eq(Call("length", w), Sub(Mul(D(2), Add(m, D(1))), D(1))),
                And(Eq(Call("support", w), support), full))));
        return Disp(All("m", Call("Nat"), Implies(Le(D(3), m), All("z", Call("Configuration", m), conclusion))));
    }

    private static Formula FullInventoryFormula()
    {
        Formula m = F.Id("m"), z = F.Id("z"), g = F.Id("g"), w = F.Id("w");
        Formula e = F.Id("e"), config = Call("Configuration", m);
        Formula gen = new Formula.Logic(Eq(g, Call("a", m)), FormulaLogicOperator.Or, Eq(g, Call("b", m)));
        Formula support = All("v", config, new Formula.Logic(
            Call("mem", F.Id("v"), Call("support", w)), FormulaLogicOperator.Iff, Call("Circle", z, F.Id("v"))));
        Formula assumptions = And(gen, And(Call("IsPath", w),
            And(Eq(Call("length", w), Sub(Mul(D(2), Add(m, D(1))), D(1))), support)));
        Formula conclusion = All("e", Call("Sym2Type", config), new Formula.Logic(
            Call("mem", e, Call("edges", w)), FormulaLogicOperator.Iff,
            And(Call("NativeCircleEdge", z, e), new Formula.Not(
                Eq(e, Call("Sym2", z, Call("rightMultiply", z, g)))))));
        return Disp(All("m", Call("Nat"), Implies(Le(D(3), m), All("z", config, All("g", config,
            All("w", Call("Walk", Call("nativeABGraph", m), z, Call("rightMultiply", z, g)),
                Implies(assumptions, conclusion)))))));
    }

    private static Formula InventoryFormula()
    {
        Formula m = F.Id("m"), z = F.Id("z"), g = F.Id("g"), w = F.Id("w");
        Formula x = F.Id("x"), h = F.Id("h"), config = Call("Configuration", m);
        Formula gen(Formula v) => new Formula.Logic(Eq(v, Call("a", m)),
            FormulaLogicOperator.Or, Eq(v, Call("b", m)));
        Formula edge(Formula v, Formula k) => Call("Sym2", v, Call("rightMultiply", v, k));
        Formula support = All("v", config,
            new Formula.Logic(Call("mem", F.Id("v"), Call("support", w)),
                FormulaLogicOperator.Iff, Call("Circle", z, F.Id("v"))));
        Formula assumptions = And(gen(g), And(Call("IsPath", w),
            And(Eq(Call("length", w), Sub(Mul(D(2), Add(m, D(1))), D(1))), support)));
        Formula conclusion = All("x", config, All("h", config,
            Implies(And(Call("Circle", z, x), gen(h)),
                new Formula.Logic(Call("mem", edge(x, h), Call("edges", w)),
                    FormulaLogicOperator.Iff, new Formula.Not(Eq(edge(x, h), edge(z, g)))))));
        return Disp(All("m", Call("Nat"), Implies(Le(D(3), m),
            All("z", config, All("g", config,
                All("w", Call("Walk", Call("nativeABGraph", m), z,
                    Call("rightMultiply", z, g)), Implies(assumptions, conclusion)))))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.Equal, r);
    private static Formula Le(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.LessThanOrEqual, r);
    private static Formula And(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.And, r);
    private static Formula Implies(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.Implies, r);
    private static Formula Add(Formula l, Formula r) => new Formula.Binary(l, FormulaBinaryOperator.Add, r);
    private static Formula Sub(Formula l, Formula r) => new Formula.Binary(l, FormulaBinaryOperator.Subtract, r);
    private static Formula Mul(Formula l, Formula r) => new Formula.Binary(l, FormulaBinaryOperator.Multiply, r);
}
