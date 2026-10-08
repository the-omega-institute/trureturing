using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Budget;

internal sealed class FinitePositiveIntervalControlDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite stationary unit table realizes positive interval sensing, recovers "
            + "both source labels, and attains its logarithmic worst read count.",
        H("Finite Stationary Positive Interval Control"),
        Blocks(
            Paragraph(Text(
                "Fix natural p>=2 and P>0. Set H=clog(2,P), B=H(P-1), and X=ZMod(pP). "
                    + "The physical source starts at the unknown x. A wait adds one to the "
                    + "source and returns no information; a read preserves the source and "
                    + "returns floor([s]_(pP)/P). The table has one common Start control.")),
            Paragraph(Text(
                "Apart from Start, a control stores a first digit in Fin(p), an ordered "
                    + "pair of interval endpoints in Fin(P), an elapsed count in Fin(B+1), "
                    + "a remaining-wait counter in Fin(P), and a mode in Fin(3). The modes "
                    + "are Wait, Read, and Done. Every changing field belongs to this finite "
                    + "carrier Q. The fixed action, wait successor, read successor, and output "
                    + "tables use only these fields and, for a read successor, the actual digit. "
                    + "Write Q=Control(p,P,B) and C for this fixed table.")),
            Paragraph(Text(
                "The first read stores its digit and the full interval. A singleton enters "
                    + "Done; otherwise the control enters Wait with the positive phase distance "
                    + "minus one in the countdown. Each Wait performs one source increment, "
                    + "increments the stored elapsed count, and either decreases the countdown "
                    + "or enters Read when it was zero. Read splits the interval at its midpoint, "
                    + "using the retained digit and stored elapsed count to decode the actual "
                    + "answer. The successor is Done for a singleton and otherwise Wait. "
                    + "Waiting requires the elapsed count to be below B; a final read remains "
                    + "available at B. Other nonterminal rows perform a read and enter Done, "
                    + "so all nominal rows and all digits have a defined successor.")),
            Paragraph(Text(
                "For a natural list w, Unit(w) concatenates W repeated w_i times and one R "
                    + "for each entry. Follows(C,c,v,z) recursively checks that each letter of v "
                    + "is exactly the action prescribed at c, then applies the corresponding "
                    + "unit transition. It ends at z with no additional action. RCount and "
                    + "WCount count the corresponding letters. Initial(q)=bP+L modulo pP "
                    + "and Current(q)=bP+L+E modulo pP are fixed functions of the terminal "
                    + "control. All letters in R::Unit(w) are actual source actions.")),
            Describe.Lean(
                DescribeId.Create("finite-positive-interval-control"),
                DeclarationHandle.Create("D5/S3/Observer/Budget/FinitePositiveIntervalControl.result"),
                H("Finite execution, both outputs, exact counts, and the singleton case"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Induction on the interval tree constructs the same physical execution "
                        + "as its query semantics. A countdown segment executes exactly its "
                        + "positive number of unit waits, with every intermediate elapsed count "
                        + "inside Fin(B+1). The ensuing read selects the correct child interval. "
                        + "The budget inequality guarantees that the waiting guard succeeds, "
                        + "including a segment whose last wait reaches B. At a leaf, the two "
                        + "fixed outputs equal the original and current sources. The original "
                        + "source P-1 follows the rightmost path and attains exactly 1+H reads. "
                        + "For P=1 the sole first read immediately reaches the correct halt control."))),
                DescribeRole.Theorem))));

    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula All(Formula x, Formula domain, Formula body) =>
        Seq(Forall, Sp, x, Sp, Colon, Sp, domain, Comma, Sp, body);
    private static Formula Some(Formula x, Formula domain, Formula body) =>
        Seq(Exists, Sp, x, Sp, Colon, Sp, domain, Comma, Sp, body);

    private static Formula Statement()
    {
        Formula p = F.Id("p"), P = F.Id("P"), x = F.Id("x"), q = F.Id("q"),
            w = F.Id("w"), v = F.Id("v");
        Formula h = Call("clog", D(2), P), B = Seq(h, Times, Grp(Seq(P, Minus, D(1))));
        Formula Q = Call("Control", p, P, B), C = Call("table", p, P, B);
        Formula X = Call("ZMod", Seq(p, Times, P));
        Formula word = Call("Cons", F.Id("R"), Call("Unit", w));
        Formula sum = Call("sum", w), len = Call("length", w);
        Formula trace = Call("Follows", C, Call("Pair", x, F.Id("Start")), word,
            Call("Pair", Call("Current", q), q));
        Formula halt = Seq(Call("action", C, q), Eq, F.Id("halt"));
        Formula waits = All(v, N(), Seq(v, InMacro, w, Implies,
            Grp(Seq(D(0), Lt, v, Land, v, Lt, P))));
        Formula behavior = All(x, X, Some(q, Q, Some(w, Call("List", N()), Grp(Seq(
            trace, Land, halt, Land, Call("Initial", q), Eq, x, Land,
            Call("Current", q), Eq, Call("Add", x, Call("Cast", sum, X)), Land,
            len, Leq, h, Land, sum, Leq, B, Land, waits, Land,
            Call("RCount", word), Eq, D(1), Plus, len, Land,
            Call("WCount", word), Eq, sum)))));
        Formula attained = Some(x, X, Some(q, Q, Some(w, Call("List", N()),
            Grp(Seq(trace, Land, halt, Land, Call("RCount", word), Eq, D(1), Plus, h)))));
        Formula singleton = Seq(P, Eq, D(1), Implies, All(x, X, Some(q, Q, Grp(Seq(
            Call("Follows", C, Call("Pair", x, F.Id("Start")), Call("Singleton", F.Id("R")),
                Call("Pair", x, q)), Land, halt, Land, Call("Initial", q), Eq, x,
                Land, Call("Current", q), Eq, x)))));
        return Disp(All(p, N(), All(P, N(), Seq(
            Grp(Seq(D(2), Leq, p, Land, D(0), Lt, P)), Implies,
            Grp(Seq(Call("Finite", Q), Land,
                Call("action", C, F.Id("Start")), Eq, F.Id("R"), Land,
                Grp(behavior), Land, Grp(attained), Land, Grp(singleton)))))));
    }
}
