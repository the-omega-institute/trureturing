using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class PrefixReversalInsertionLayerPartitionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversalInsertionLayerPartition.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Over a directed base distinct from its reverse, every actual configuration in the complete insertion layer belongs to exactly one independently specified positive directed child domain.",
        H("Complete Insertion-Layer Partition"),
        Blocks(
            Paragraph(Text(
                "Configuration(m) is the permutation type of Fin(m+1). The label v(i) occupies position i, "
                + "and configurationCycle(v) is its full tuple modulo rotation. Cycle identifies rotations "
                + "and retains the direction of the list. For a finite label set S, erase(S,C) restricts "
                + "the actual directed circle C to labels outside S. Deletion of x restricts to labels different from x.")),
            Paragraph(Text(
                "Layer(S,P,v) means erase(S,configurationCycle(v)) equals P or reverse(P). "
                + "ChildCircle(S,x,P) is the subtype of directed circles D that have no repeated labels, "
                + "contain a label y exactly when y is outside S, satisfy erase(S,D)=D, and satisfy delete(x,D)=P. "
                + "The deletion equality fixes the positive direction of the child. For such a subtype element D, "
                + "ChildDomain(D,v) means Layer(S,D.val,v). These objects are defined from complete native "
                + "configurations and actual deletion, before choosing any path or graph.")),
            Node("native-residual-supplier", "Every Full Residual Has an Actual Native Supplier",
                "nativeResidual_surjective", NativeResidualFormula(),
                "For every natural m, every finite selected set S and every directed residual D on Fin(m+1), "
                + "assume D has no repeated labels and y belongs to D exactly when y is outside S. "
                + "There is an actual Configuration(m) whose restriction outside S is precisely D. "
                + "Choose a representative list of D and prepend the labels of S once. The two lists are disjoint; "
                + "their concatenation contains every native label exactly once. Its list get-equivalence gives "
                + "a permutation of Fin(m+1). Filtering out S recovers the complete original representative of D."),
            Node("unique-directed-child", "The Complete Independent Child Partition",
                "insertionLayer_partition", PartitionFormula(),
                "For every natural m, selected set S, label x, directed base P different from its reverse, "
                + "and actual native configuration v, membership in Layer(insert(x,S),P) is equivalent to "
                + "membership in exactly one independently admissible ChildCircle(S,x,P) supplier domain. "
                + "Erase S from the actual configuration. Deleting x from that residual gives P or reverse(P); "
                + "reverse the whole residual in the latter case to obtain a positive child. Its support is "
                + "exactly the labels outside S and it has no duplicates. Two positive children sharing a native "
                + "vertex must coincide: opposite residual orientations would imply P=reverse(P). "
                + "The formula expresses the unique existential as existence together with equality of every "
                + "other child whose full independent supplier domain contains the same v."),
            Describe.Lean(DescribeId.Create("complete-layer-equivalence"),
                DeclarationHandle.Create(Prefix + "insertionLayerEquiv"),
                H("The Actual Partition Equivalence"),
                StatementSource.FromAuthor(EquivalenceFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a directed base P distinct from its reverse, insertionLayerEquiv(hP) is an equivalence "
                    + "from the entire native parent layer to the dependent sum of the independently defined child domains. "
                    + "The forward map chooses the unique positive child of the actual native vertex and keeps that vertex. "
                    + "The inverse forgets the child index and keeps the vertex. The partition proves the two inverse laws. "
                    + "The displayed brace expressions are subtypes, and Sigma is the dependent sum over ChildCircle. "
                    + "No graph, path, Hamilton cycle or recursive spanning construction is an input or conclusion."))),
                DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula NativeResidualFormula()
    {
        Formula m = F.Id("m"), s = F.Id("S"), d = F.Id("D"), y = F.Id("y"), v = F.Id("v");
        Formula labels = Call("Fin", Add(m, D(1)));
        Formula exactSupport = All(Iff(Mem(y, d), Not(Mem(y, s))), ("y", labels));
        Formula conclusion = Ex("v", Call("Configuration", m),
            Eq(Call("erase", s, Call("configurationCycle", v)), d));
        return Disp(All(conclusion,
            ("m", Call("Nat")), ("S", Call("Finset", labels)), ("D", Call("Cycle", labels)),
            ("hn", Call("Nodup", d)), ("hm", exactSupport)));
    }

    private static Formula PartitionFormula()
    {
        Formula m = F.Id("m"), s = F.Id("S"), x = F.Id("x"), p = F.Id("P"), v = F.Id("v");
        Formula d = F.Id("D"), e = F.Id("E"), labels = Call("Fin", Add(m, D(1)));
        Formula children = Call("ChildCircle", s, x, p);
        Formula uniqueChild = Ex("D", children, And(Call("ChildDomain", d, v),
            All(Implies(Call("ChildDomain", e, v), Eq(e, d)), ("E", children))));
        Formula conclusion = Iff(Call("Layer", Call("insert", x, s), p, v), uniqueChild);
        return Disp(All(conclusion,
            ("m", Call("Nat")), ("S", Call("Finset", labels)), ("x", labels),
            ("P", Call("Cycle", labels)), ("hP", Ne(p, Call("reverse", p))),
            ("v", Call("Configuration", m))));
    }

    private static Formula EquivalenceFormula()
    {
        Formula m = F.Id("m"), s = F.Id("S"), x = F.Id("x"), p = F.Id("P");
        Formula v = F.Id("v"), d = F.Id("D"), labels = Call("Fin", Add(m, D(1)));
        Formula parent = Subtype("v", Call("Configuration", m), Call("Layer", Call("insert", x, s), p, v));
        Formula child = Subtype("v", Call("Configuration", m), Call("ChildDomain", d, v));
        Formula children = Seq(Open, Sigma, Sp, d, Colon, Sp, Call("ChildCircle", s, x, p), Comma, Sp, child, Close);
        Formula type = Call("Equiv", parent, children);
        Formula statement = Seq(Call("insertionLayerEquiv", F.Id("hP")), Colon, Sp, type);
        return Disp(All(statement,
            ("m", Call("Nat")), ("S", Call("Finset", labels)), ("x", labels),
            ("P", Call("Cycle", labels)), ("hP", Ne(p, Call("reverse", p)))));
    }

    private static Formula Subtype(string variable, Formula domain, Formula predicate) =>
        Seq(OpenBrace, F.Id(variable), Colon, Sp, domain, Sp, Mid, Sp, predicate, CloseBrace);

    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(Formula body, params (string Name, Formula Domain)[] variables)
    {
        for (var i = variables.Length - 1; i >= 0; i--)
            body = new Formula.Bind(FormulaQuantifier.ForAll,
                FormulaIdentifier.Create(variables[i].Name), variables[i].Domain, body);
        return body;
    }
    private static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.Equal, r);
    private static Formula Ne(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.NotEqual, r);
    private static Formula Mem(Formula x, Formula domain) => new Formula.Relation(x, FormulaRelationOperator.MemberOf, domain);
    private static Formula Not(Formula p) => new Formula.Not(p);
    private static Formula And(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.And, r);
    private static Formula Iff(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.Iff, r);
    private static Formula Implies(Formula l, Formula r) =>
        new Formula.Logic(Seq(Open, l, Close), FormulaLogicOperator.Implies, Seq(Open, r, Close));
    private static Formula Add(Formula l, Formula r) => new Formula.Binary(l, FormulaBinaryOperator.Add, r);
}
