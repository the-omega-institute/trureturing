using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeJ2WordsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2Words.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Five literal native J2 generator words reach their independently specified actual ports and have the exact required lengths.",
        H("The Five Literal Native J2 Words"),
        Blocks(
            Paragraph(Text(
                "Configurations are actual permutations of Fin(m+1), with reversals a, b and c of lengths "
                + "m+1, m and m-1. Here m is at least five, p=0, q=m, v=m-1 and A=(1,...,m-2). "
                + "The actual right ports are R0=(q,p,A,v), R1=(p,A,q,v) and R2=(A,q,p,v). "
                + "Each left port Li is Ri*b, and bar exchanges the actual label values p and q by left "
                + "multiplication. These ports are defined independently of the words.")),
            Paragraph(Text(
                "Write Uk=(ab)^k a and H=Um, retaining the actual generator lists. In index order 0,...,4 "
                + "the words are abc U(m-2) c U(m-1); (ab)^(m-1) (cH)^(m-3) ca; "
                + "a (cH)^(m-3) caba; ac U(m-2); and abc U(m-1). Their required port pairs are "
                + "R0 to R2, L0 to bar(L1), R1 to bar(L2), L2 to bar(R2), and bar(R0) to bar(R1).")),
            Node("native-j2-word-endpoints", "native_j2_word_endpoints", "All Five Actual Endpoint Identities",
                EndpointsFormula(),
                "For every m at least five and every i in Fin(5), wordStart(m,i) multiplied by the actual "
                + "list product of word(m,i) equals wordFinish(m,i). The proof reuses uWord_product, "
                + "computes H=b, obtains (cb)^(m-3)=(bc)^3 from the earned complete E identity (bc)^m=1, "
                + "and checks the remaining native Fin coordinates extensionally. The first and fourth "
                + "words use the actual endpoint-swap/rotation identity, reversal conjugation and the "
                + "three-label transposition braid; sizes five through seven use kernel decide. "
                + "No endpoint identity is assumed."),
            Node("native-j2-word-lengths", "native_j2_word_lengths", "All Five Exact Literal Edge Counts",
                LengthsFormula(),
                "For every m at least five and every i in Fin(5), the actual list length is the independently "
                + "specified wordLength(m,i). In index order these lengths are 4m, 2m^2-2m-6, "
                + "2m^2-4m-1, 2m-1 and 2m+2. The proof counts the literal append and repetition lists, "
                + "using uWord_length for their alternating native blocks."),
            Paragraph(Text(
                "Endpoints and lengths alone do not prove that these words use surviving edges of the "
                + "specific F2 factor, avoid the six J2 marked cuts, form complete path components, or "
                + "yield an all-size Hamilton cycle. Those edge-inventory and whole-component obligations "
                + "remain separate.")))));

    private static DocumentBlock Node(string id, string selector, string title, Formula statement, string proof) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + selector), H(title),
            StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(proof))), DescribeRole.Theorem);

    private static Formula EndpointsFormula()
    {
        Formula m = F.Id("m"), i = F.Id("i");
        return Scoped(m, Eq(Call("mul", Call("wordStart", m, i), Call("prod", Call("word", m, i))),
            Call("wordFinish", m, i)));
    }

    private static Formula LengthsFormula()
    {
        Formula m = F.Id("m"), i = F.Id("i");
        return Scoped(m, Eq(Call("length", Call("word", m, i)), Call("wordLength", m, i)));
    }

    private static Formula Scoped(Formula m, Formula body) =>
        Disp(All("m", Call("Nat"), Implies(Le(D(5), m), All("i", Call("Fin", D(5)), body))));
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.Equal, r);
    private static Formula Le(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.LessThanOrEqual, r);
    private static Formula Implies(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.Implies, r);
}
