using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class TriangularSharedImplementationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.";
    private static Formula V(string s) => F.Id(s);
    private static Formula Fn(string s, params Formula[] args) => Call(s, args);
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula All(string s, Formula type, Formula body) =>
        Par(Seq(Forall, Sp, V(s), Colon, Sp, type, Comma, Sp, body));
    private static Formula Some(string s, Formula type, Formula body) =>
        Par(Seq(Exists, Sp, V(s), Colon, Sp, type, Comma, Sp, body));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Rel(Formula a, Formula relation, Formula b) => Seq(a, Sp, relation, Sp, b);
    private static Formula And(params Formula[] clauses)
    {
        var items = new List<Formula>();
        foreach (var c in clauses)
        {
            if (items.Count > 0) items.AddRange([Sp, Land, Sp, RowBreak]);
            items.Add(Par(c));
        }
        return Seq([.. items]);
    }
    private static DocumentBlock Definition(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("triangular-shared-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One-bit terminal pairs can be shared in every legal stationary triangular table.",
        H("Shared Triangular Slot Implementation"), Blocks(
            Definition("Table", "Stationary legal actions", "For each m, a table fixes one action "
                + "at each aggregate state. At every 0 <= r < e <= m with e positive, the action "
                + "satisfies the triangular legality conditions. The aggregate state and its successor "
                + "are those of reduced triangular paths, including zero residual self-loops."),
            Definition("Slot", "Original active slots", "A slot has coordinates (e,r,k) with "
                + "0 <= e <= m, 0 <= r < e and 0 <= k < r. The last condition excludes r=0. "
                + "Thus these are exactly the triples 1 <= r < e <= m and 0 <= k < r."),
            Definition("aggregate", "Aggregate coordinates", "The aggregate of (e,r,k) is (r,e)."),
            Definition("Immediate", "Two immediate children", "A slot is immediate precisely when "
                + "e <= 2r and k < floor(e/2). In an odd layer e=2j+1, k=j is excluded."),
            Definition("SharedActive", "Shared and singleton activities", "The shared active carrier "
                + "is the disjoint union of P_k for k < floor(m/2) and one V_(r,e,k) for every "
                + "non-immediate original slot. Terminals form a separate copy of Fin(m)."),
            Definition("color", "Activity and terminal colors", "All activity states have color none. "
                + "Terminal i has color some(i), so terminals are pairwise distinct in color. "
                + "The index i in Fin(m) denotes the source label i+1."),
            Definition("root", "Original root", "For every m >= 2 the root is the active slot (1,m,0)."),
            Definition("outputCount", "Length of the ordered output list", "For the one action the "
                + "output count q is e; for zero(h) it is h. In particular h=0 gives an empty list."),
            Definition("outputLabel", "Ordered labels", "At zero-based list position z, the one "
                + "action outputs label index z, while zero(h) outputs e-h+z. These correspond to "
                + "the one-based lists (1,...,e) and (e-h+1,...,e)."),
            Definition("originalStep", "Original paid-bit transition", "At (r,e,k), read one bit u "
                + "and set z=2k+u. If z<q, return the label at ordered list position z. Otherwise "
                + "continue at (r',e',z-q), using the prescribed aggregate successor. This branch "
                + "satisfies z-q<r', so zero residual states are never active slots. Terminals have "
                + "absorbing auxiliary transitions and do not consume further paid bits."),
            Definition("projection", "Immediate-pair projection", "Every immediate slot of index "
                + "k projects to P_k. Every other slot projects to its own singleton V_(r,e,k). "
                + "Each terminal projects to the terminal with the same label."),
            Definition("sharedStep", "Fixed ordered shared transitions", "The two children of P_k "
                + "are terminal indices 2k and 2k+1. A singleton uses the projection of its original "
                + "successor. Terminal transitions remain absorbing."),
            Definition("trace", "Prefixes of a stream", "For a transition delta, start s, stream "
                + "omega and natural n, trace is the state after the first n bits, in their order."),
            Definition("FirstStop", "First stopping response", "FirstStop(delta,c,s,omega,i,n) means "
                + "the state after n bits has terminal color some(i), and every shorter prefix has "
                + "activity color none. An initially terminal state stops at length zero."),
            Definition("charged", "Paid prefix length", "The charge through prefix length n counts "
                + "exactly those positions j<n whose source state is active. Each such edge costs "
                + "one bit; absorbing terminal extensions cost zero."),
            Definition("Nonstop", "Nontermination", "Nonstop means every finite prefix has "
                + "activity color none. It is a property of the same actual infinite stream."),
            Definition("ReachableActive", "Root-reachable activities", "These are shared activities "
                + "that occur after a finite input word from the projected root. Unreachable "
                + "activities contribute to the full carrier count but not to this restriction."),
            Definition("bound", "General sufficient activity bound", "B(m)=m(m-1)(m+1)/6 "
                + "minus the sum of floor(e/2)^2 for e=0,...,m, plus floor(m/2). "
                + "The zero summand makes this the same sum as e=1,...,m. All divisions are "
                + "natural-number divisions; the subtracted count does not exceed the original slot count."),
            Describe.Lean(DescribeId.Create("triangular-shared-implementation"),
                DeclarationHandle.Create(Prefix + "result"), H("Complete stream preservation and activity count"),
                StatementSource.FromAuthor(Disp(ResultFormula())), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every m >= 2 and every legal stationary table f, there are "
                        + "a surjective projection pi and a fixed ordered shared transition delta. "
                        + "The projection preserves activity and every terminal label, and it commutes "
                        + "with each bit transition. For every infinite stream, the first terminal "
                        + "label and stopping length agree, all prefix charges agree, and nontermination "
                        + "agrees. At a first stop of length n, the original charge is n; hence so is "
                        + "the shared charge. The full shared activity carrier has exactly B(m) states, "
                        + "its root-reachable activity carrier has at most B(m), and there are m terminals.")),
                    Paragraph(Text("At a fixed layer e, write j=floor(e/2). The immediate slots are "
                        + "in bijection with Fin(j) times Fin(j): the first coordinate selects "
                        + "r=e-j,...,e-1 and the second selects k=0,...,j-1. Thus j^2 original "
                        + "slots are replaced. Every P_k has an original representative with "
                        + "e=2(k+1) and r=k+1. The ordered terminal pair is independent of which "
                        + "representative is used. Summing the remaining singletons and adding "
                        + "the shared pairs gives B(m). The even and odd endpoints yield the "
                        + "two displayed cubic formulas. This is a sufficient bound, with no "
                        + "minimality or sharpness assertion."))), DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var nat = Seq(Mathbb, Grp(V("N")));
        var m = V("m"); var f = V("f"); var pi = V("pi"); var delta = V("delta");
        var s = V("s"); var u = V("u"); var omega = V("omega"); var i = V("i"); var n = V("n");
        var q = V("q"); var bits = Fn("Fin", D(2)); var labels = Fn("Fin", m);
        var original = Fn("Original", m); var shared = Fn("Shared", m);
        var start = Fn("root", m); var imageStart = Fn("pi", start);
        var raw = Fn("originalStep", f);
        var response = All("omega", Arrow(nat, bits), All("i", labels, All("n", nat,
            Rel(Fn("FirstStop", raw, V("color"), start, omega, i, n), Iff,
                Fn("FirstStop", delta, V("color"), imageStart, omega, i, n)))));
        var bills = All("omega", Arrow(nat, bits), All("n", nat,
            Equal(Fn("charged", raw, V("color"), start, omega, n),
                Fn("charged", delta, V("color"), imageStart, omega, n))));
        var paid = All("omega", Arrow(nat, bits), All("i", labels, All("n", nat,
            Imp(Fn("FirstStop", raw, V("color"), start, omega, i, n),
                Equal(Fn("charged", raw, V("color"), start, omega, n), n)))));
        var nonstop = All("omega", Arrow(nat, bits),
            Rel(Fn("Nonstop", raw, V("color"), start, omega), Iff,
                Fn("Nonstop", delta, V("color"), imageStart, omega)));
        var cube = new Formula.Power(q, D(3)); var square = new Formula.Power(q, D(2));
        var even = Equal(Fn("B", Seq(D(2), Cdot, q)),
            new Formula.Fraction(Seq(D(2), Cdot, cube, Plus, q), D(3)));
        var odd = Equal(Fn("B", Seq(D(2), Cdot, q, Plus, D(1))),
            new Formula.Fraction(Seq(D(2), Cdot, cube, Plus, D(3), Cdot, square, Plus, D(4), Cdot, q), D(3)));
        return All("m", nat, Imp(Rel(m, Ge, D(2)), All("f", Fn("Table", m),
            Some("pi", Arrow(original, shared), Some("delta", Arrow(shared, Arrow(bits, shared)), And(
                Fn("Surjective", pi),
                All("s", original, Equal(Fn("color", Fn("pi", s)), Fn("color", s))),
                All("s", original, All("u", bits,
                    Equal(Fn("pi", Fn("originalStep", f, s, u)), Fn("delta", Fn("pi", s), u)))),
                response, bills, paid, nonstop,
                Equal(Fn("card", Fn("SharedActive", m)), Fn("B", m)),
                Rel(Fn("card", Fn("ReachableActive", delta, imageStart)), Le, Fn("B", m)),
                Equal(Fn("card", labels), m),
                All("q", nat, Imp(Rel(q, Ge, D(1)), And(even, odd)))))))));
    }
}
