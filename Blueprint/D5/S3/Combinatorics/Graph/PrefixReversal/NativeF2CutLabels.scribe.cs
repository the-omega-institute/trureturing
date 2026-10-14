using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeF2CutLabelsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeF2CutLabels.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete unmarked F2 cut set has exactly two a edges, a complete geometric b-edge classification, and selected terminal labels at every endpoint.",
        H("Literal F2 Cut Generators and Endpoint Labels"),
        Blocks(
            Paragraph(Text(
                "Configurations are actual permutations of Fin(m+1). The selected labels "
                + "are p=0 and q=FinLast(m). MarkerSwap(m) is the actual transposition "
                + "Equiv.swap(0,FinLast(m)). F2DeletedEdge is the already earned complete "
                + "literal T/E cut set of the unmarked actual F2 cycle.")),
            Describe.Lean(DescribeId.Create("native-f2-a-cut-classification"),
                DeclarationHandle.Create(Prefix + "native_f2_a_cut_classification"),
                H("Exactly Two Actual a Edges Are Cut"),
                StatementSource.FromAuthor(ACutFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every m at least four and every configuration x, the a edge "
                    + "from x to xa belongs to F2DeletedEdge exactly when it is the "
                    + "undirected edge from 1 to a or the edge from MarkerSwap to "
                    + "MarkerSwap*a. Actual generator uniqueness excludes every b cut. "
                    + "The T owner index has generator a precisely at its last two "
                    + "lower indices. The first cut start is 1; the second is normalized "
                    + "to MarkerSwap by the existing actual T half-word product theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-f2-deleted-edge-endpoint-label"),
                DeclarationHandle.Create(Prefix + "native_f2_deleted_edge_endpoint_label"),
                H("Every Cut Endpoint Has Last Label p or q"),
                StatementSource.FromAuthor(EndpointFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every m at least four, every edge in F2DeletedEdge and every "
                    + "one of its actual endpoints v, the last label of v is 0 or "
                    + "FinLast(m). The two a cuts have these labels at both endpoints. "
                    + "Every other lower or remaining-supplier cut is a b edge ending "
                    + "in 0; every noncore upper cut is a b edge ending in FinLast(m). "
                    + "The actual b permutation fixes the final coordinate, and the "
                    + "actual bc powers preserve each gap anchor's final label. These "
                    + "facts classify both endpoint orientations of every literal cut."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-f2-b-cut-classification"),
                DeclarationHandle.Create(Prefix + "native_f2_b_cut_classification"),
                H("The Three Exact Circle and Star Conditions for b Cuts"),
                StatementSource.FromAuthor(BCutFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every m at least four and every actual configuration x, "
                        + "the b edge from x to xb belongs to the complete literal F2 "
                        + "cut set exactly when one of three independent geometric "
                        + "conditions holds. First, x lies in a lowerPort(j) native "
                        + "circle and its last label is zero. Second, x lies in an "
                        + "upperPort(j) native circle and its last label is FinLast(m). "
                        + "Third, x lies in the full remaining supplier star of "
                        + "contactAnchor(j) and its last label is zero. Each index j "
                        + "ranges over Fin(m-2). No F2 domain membership is assumed.")),
                    Paragraph(Text(
                        "Forward classification uses actual undirected generator "
                        + "uniqueness to exclude the two lower a cuts. The other T "
                        + "cut starts normalize to their literal lower and upper ports. "
                        + "Supplier cuts range over every gap, including gap zero. "
                        + "Backward classification uses the uniqueness of the b edge "
                        + "at an anchor's last label in a complete native circle; "
                        + "the complete supplier circle partition then covers every "
                        + "configuration in the supplier-star case."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Combining the endpoint label condition with the actual native edge "
                + "inventory retains any native edge incident to a configuration whose "
                + "last label differs from p and q. The later six v-marked cuts are "
                + "additional cuts and are not part of this unmarked F2 classification.")))));

    private static Formula ACutFormula()
    {
        Formula m = F.Id("m"), x = F.Id("x");
        Formula a = Call("a", m), swap = Call("MarkerSwap", m);
        Formula edge = Call("Sym2Pair", x, Call("Mul", x, a));
        Formula alternatives = new Formula.Logic(Eq(edge, Call("Sym2Pair", Call("One"), a)),
            FormulaLogicOperator.Or, Eq(edge, Call("Sym2Pair", swap, Call("Mul", swap, a))));
        return Disp(All("m", Call("Nat"), Implies(Le(D(4), m),
            All("x", Call("Configuration", m), new Formula.Logic(Call("F2DeletedEdge", m, edge),
                FormulaLogicOperator.Iff, alternatives)))));
    }

    private static Formula EndpointFormula()
    {
        Formula m = F.Id("m"), e = F.Id("e"), v = F.Id("v");
        Formula labels = new Formula.Logic(Eq(Call("LastLabel", m, v), D(0)),
            FormulaLogicOperator.Or, Eq(Call("LastLabel", m, v), Call("FinLast", m)));
        return Disp(All("m", Call("Nat"), Implies(Le(D(4), m),
            All("e", Call("Sym2", Call("Configuration", m)), All("v", Call("Configuration", m),
                Implies(new Formula.Logic(Call("F2DeletedEdge", m, e), FormulaLogicOperator.And,
                    Call("Member", v, e)), labels))))));
    }

    private static Formula BCutFormula()
    {
        Formula m = F.Id("m"), x = F.Id("x"), j = F.Id("j");
        Formula index = Call("Fin", Call("NatSub", m, D(2)));
        Formula last = Call("LastLabel", m, x);
        Formula lower = Exists("j", index, And(Call("Circle", Call("lowerPort", j), x),
            Eq(last, D(0))));
        Formula upper = Exists("j", index, And(Call("Circle", Call("upperPort", j), x),
            Eq(last, Call("FinLast", m))));
        Formula supplier = Exists("j", index,
            And(Call("SupplierStar", Call("contactAnchor", j), x), Eq(last, D(0))));
        Formula cut = Call("F2DeletedEdge", m,
            Call("Sym2Pair", x, Call("Mul", x, Call("b", m))));
        return Disp(All("m", Call("Nat"), Implies(Le(D(4), m),
            All("x", Call("Configuration", m),
                new Formula.Logic(cut, FormulaLogicOperator.Iff,
                    new Formula.Logic(lower, FormulaLogicOperator.Or,
                        new Formula.Logic(upper, FormulaLogicOperator.Or, supplier)))))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
