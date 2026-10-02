using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class TerminalGcdAcquisitionCostDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/TerminalGcdAcquisitionCost.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The minimum worst number of same-source terminal gcd experiments for exact "
            + "composition recovery is twice the largest prime-power digit budget.",
        H("Exact acquisition by positive replacement and graft words"),
        Blocks(
            Describe.Lean(DescribeId.Create("terminal-gcd-acquisition-cost"),
                DeclarationHandle.Create(Prefix + "terminal_gcd_acquisition_cost"),
                H("The minimum is attained for every positive modulus"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The actual source is an unknown pair v=(a,b) of natural numbers, "
                            + "including (0,0). Replacement is R(a,b)=(b,a+b) and grafting "
                            + "is G(a,b)=(a+1,b). A word is a finite Boolean list, with true "
                            + "meaning R and false meaning G, applied in chronological order. "
                            + "Its sole response is gcd(2a'+3b',H) at the terminal pair. "
                            + "Every experiment starts at the same v. Each selected list, "
                            + "including the empty list, costs one query. There are no initial "
                            + "or intermediate responses.")),
                    Paragraph(Text(
                        "A(H) consists of finite budgets K for deterministic history "
                            + "selectors whose executions terminate with (a,b) modulo H "
                            + "on every actual source and whose complete traces have length "
                            + "at most K on every source. A selector chooses a word or returns "
                            + "the residue pair from the complete preceding history. A fuel "
                            + "function merely certifies termination; it supplies no observation. "
                            + "Q(H) is the infimum of A(H). The IsLeast assertion also proves "
                            + "that A(H) is nonempty and that its infimum is attained.")),
                    Paragraph(Text(
                        "Write B(H)=max over prime divisors p of H of v_p(H)(p-1), with "
                            + "the empty maximum zero. For H>1, Chinese remaindering identifies "
                            + "ZMod H with the product of ZMod(p^e) over p^e exactly dividing H. "
                            + "Fix one common k for a scalar stage, recovering y=qM^k v, "
                            + "where q=(2,3) and M sends (a,b) to (b,a+b). Only local shifts "
                            + "are combined; local row vectors are never selected independently.")),
                    Paragraph(Text(
                        "Each prime axis has an identifying residue protocol with at most "
                            + "e(p-1) queries on every target, obtained from the complete "
                            + "depth-zero residue node. In each simultaneous round an active "
                            + "axis supplies its next center. A stopped axis supplies center "
                            + "zero and remains stopped, discarding that round's response. "
                            + "Equality of synchronized histories implies equality of every "
                            + "local history, including axes that stop early. Combining the "
                            + "centers by CRT uses one actual word per round, so B(H) rounds "
                            + "identify the scalar on all axes.")),
                    Paragraph(Text(
                        "For L=(H^2)!, the positive word W(k,c) is R^k, then "
                            + "G^((-c).val), R^(L-1), G^(c.val), and R. Since M^L is the "
                            + "identity modulo H, its terminal quantity is qM^k v+c "
                            + "modulo H. Its length is at most L+k+2(H-1). Every intermediate "
                            + "pair is nonnegative. Negative shifts only select residue "
                            + "representatives; no inverse move or additional read is used.")),
                    Paragraph(Text(
                        "Run the k=0 and k=1 stages on the same v to recover "
                            + "n=2a+3b and z=3a+5b modulo H. The determinant of their "
                            + "coefficient matrix is one, so (a,b)=(5n-3z,-3n+2z) "
                            + "modulo H. This gives a strategy of at most 2B(H) queries. "
                            + "The subtraction is residue decoding, not an operation on "
                            + "the actual source.")),
                    Paragraph(Text(
                        "For the lower bound choose p^e exactly dividing H and put D=H/p^e. "
                            + "The actual family v_x=(D x_1.val,D x_2.val), with x in "
                            + "ZMod(p^e)^2, has pairwise different target residues. "
                            + "Every word has terminal quantity A a+B b+C with fixed "
                            + "natural coefficients at that history node. On this family "
                            + "its whole response equals gcd(C,D) times p raised to the "
                            + "complete affine depth of D A x_1+D B x_2+C. The positive "
                            + "factor gcd(C,D) is known at the node and independent of x, "
                            + "including C=0, D=1, and saturated responses.")),
                    Paragraph(Text(
                        "Thus one affine-depth query reconstructs the original whole "
                            + "response and preserves every adaptive choice and charged "
                            + "query. Exact composition recovery identifies x, so the "
                            + "dimension-two affine lower bound supplies one actual source "
                            + "requiring at least 2e(p-1) queries. Choose an axis attaining "
                            + "B(H). No simultaneous attainment of separate axis worst "
                            + "histories is required. For H=1 the target is unique and a "
                            + "selector returns it with no query."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Arith/FibonacciAtomic/AffineValuationQueryLowerBound")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/Budget/ResidueHeightUpperBound")),
        ]));

    private static Formula V(string s) => F.Id(s);
    private static Formula C(string name, params Formula[] args) => Call(name, args);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Statement()
    {
        var bound = Seq(D(2), C("B", V("H")));
        var value = C("ite", Seq(V("H"), Eq, D(1)), D(0), bound);
        var result = Seq(C("IsLeast", C("A", V("H")), value), Sp, Land, Sp,
            C("Q", V("H")), Sp, Eq, Sp, value);
        return Seq(Forall, Sp, V("H"), Sp, InMacro, Sp, Mathbb, Grp(V("N")), Comma, Sp,
            Par(Seq(D(1), Sp, Le, Sp, V("H"))), Sp, Implies, Sp, Par(result));
    }
}
