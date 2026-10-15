using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeSwitchesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeSwitches.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal native T and E switching words close, and their actual prefix traces have no repeated vertex before return.",
        H("Native Alternating Switching Polygons"),
        Blocks(
            Paragraph(Text(
                "Configurations are actual permutations of Fin(m+1), and right multiplication acts on positions. "
                + "The reversals a, b and c have lengths m+1, m and m-1. Put B=bc. The halfword is the list "
                + "[a,c] followed by m-2 copies of [b,c], flattened. The T word repeats this halfword twice; "
                + "the complete E word consists of m copies of [b,c]. All repetition here preserves the literal "
                + "generator list. The trace is scanl of right multiplication, so it records every actual prefix product.")),
            Node("t-halfword-swap", "native_t_halfword_swap", "The Exact Halfword Endpoint",
                HalfwordFormula(),
                "For every m at least three, the halfword product is precisely the swap of positions zero and m. "
                + "The proof computes every power of bc on each native position, and then applies a and c. "
                + "It does not assume an endpoint matching or a finite enumeration."),
            Node("t-simple-trace", "native_t_simple_trace", "The Complete T Polygon Is Simple",
                SimpleFormula("tWord", false),
                "The T product is identity and its prefix trace with the final return removed has no repeats. "
                + "Writing tau for the endpoint swap, the trace before return is [1,a], the paired interior ports, "
                + "[tau,tau*a], and the tau-left-translates of the same interior ports. The last-label-zero group "
                + "has native coordinates (m-2,false), (m-1,true), and both orientations at all indices below m-2. "
                + "The existing coordinateEquiv proves they are distinct. Left multiplication by tau preserves "
                + "distinctness and moves their last label to m, which separates the two groups."),
            Node("e-simple-trace", "native_e_simple_trace", "Every Complete E Supplier Is Simple",
                SimpleFormula("eWord", true),
                "For every starting configuration z, the complete E word has product identity. Its actual trace "
                + "is the ordered flattened list [z*B^j,z*B^j*b], for j in Fin(m), followed by z. Each pair has "
                + "the two different native reflection coordinates at one gap; different gaps have different "
                + "coordinates. The existing coordinateEquiv therefore proves no repeat before the return."),
            Paragraph(Text(
                "These results establish actual native switching polygons. They do not establish that a toggled "
                + "factor is connected, that each cut belongs to a different complete native circle, or that the "
                + "three-generator Cayley graph has a Hamilton cycle. Those support and splicing obligations "
                + "must be proved separately.")))));

    private static DocumentBlock Node(string id, string selector, string title, Formula statement, string proof) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + selector), H(title),
            StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(proof))), DescribeRole.Theorem);

    private static Formula HalfwordFormula()
    {
        Formula m = F.Id("m");
        return Disp(All("m", Call("Nat"), Implies(Le(D(3), m),
            Eq(Call("prod", Call("tHalfWord", m)), Call("swap", D(0), Call("last", m))))));
    }

    private static Formula SimpleFormula(string word, bool supplier)
    {
        Formula m = F.Id("m"), z = supplier ? F.Id("z") : D(1);
        Formula list = Call(word, m);
        Formula trace = Call("scanl", Call("rightMultiply"), z, list);
        Formula conclusion = And(Eq(Call("prod", list), D(1)),
            Call("Nodup", Call("dropLast", trace)));
        if (supplier)
        {
            Formula ports = Call("flatten", Call("ofFn", Call("pairAtGap", z, m)));
            conclusion = And(Eq(Call("prod", list), D(1)),
                And(Eq(trace, Call("append", ports, Call("singleton", z))),
                    Call("Nodup", Call("dropLast", trace))));
            conclusion = All("z", Call("Configuration", m), conclusion);
        }
        return Disp(All("m", Call("Nat"), Implies(Le(D(3), m), conclusion)));
    }

    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.Equal, r);
    private static Formula Le(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.LessThanOrEqual, r);
    private static Formula And(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.And, r);
    private static Formula Implies(Formula l, Formula r) =>
        new Formula.Logic(l, FormulaLogicOperator.Implies, r);
}
