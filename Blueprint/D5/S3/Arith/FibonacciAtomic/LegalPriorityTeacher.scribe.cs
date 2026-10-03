using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class LegalPriorityTeacherDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula body) => Seq(Left, Open, body, Right, Close);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(variable, Colon, Sp, type)), Comma, Sp, body);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two ordered effective edges completely classify priority teachers on legal Fibonacci histories.",
        H("Priority Teachers on the Legal Five-Window Language"),
        Blocks(
            Paragraph(Text("Fix a natural n. Input(n) is Fin(n) to Window, where Window consists "
                + "of 000,100,010,101,001 written from low to high. Positions start at zero. "
                + "The unit bit is zero, terminal zero windows are allowed, and there is no End query. "
                + "Legal(x) is the existing flattened-bit Fibonacci legality predicate with false "
                + "initial bit. In particular high(x(i)) and low(x(i+1)) cannot both be true. "
                + "Null windows retain their positions.")),
            Paragraph(Text("Roles(n) consists of p,q,r in Fin(n) with p<q<r. The actual teacher "
                + "first tests high(x(p)) and low(x(q)), returning 1 when both hold. Otherwise it "
                + "tests high(x(q)) and low(x(r)), returning 2 when both hold, and 0 otherwise. "
                + "The priority of the first test is part of the function.")),
            Paragraph(Text("edge(i,j) is Some(i,j) when i+1<j and None otherwise. signature(t) "
                + "is the ordered pair (edge(p,q),edge(q,r)); the two absent entries remain distinct "
                + "positions in that pair. Adjacency forces a gate to vanish on every legal history. "
                + "An active edge is tested by putting 001 at its first position and 100 at its "
                + "second position, with 000 everywhere else. This is a legal actual input. "
                + "It activates precisely that position pair.")),
            Describe.Lean(DescribeId.Create("legal-priority-teacher-equivalence"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/LegalPriorityTeacher.result"),
                H("Complete equivalence of the actual legal-domain functions"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The equivalence holds for all n and all strict role triples. "
                    + "A first-edge probe returns 1, whereas a second-edge probe returns 2. "
                    + "The priority rule therefore prevents the other teacher's first edge from "
                    + "impersonating a second edge. A triple with both gaps at least two is determined "
                    + "by its legal-domain function. Triples with two adjacent gates all give zero. "
                    + "No sampling law, probability bound, or label-noise assumption is used."))),
                DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var n = V("n");
        var t = V("t");
        var u = V("u");
        var x = V("x");
        var equal = All(x, Call("Input", n),
            Seq(Call("Legal", x), Sp, Implies, Sp,
                EqOf(Call("teacher", t, x), Call("teacher", u, x))));
        return All(n, Seq(Mathbb, Grp(V("N"))),
            All(t, Call("Roles", n), All(u, Call("Roles", n),
                Seq(Par(equal), Sp, Iff, Sp,
                    EqOf(Call("signature", t), Call("signature", u))))));
    }
}
