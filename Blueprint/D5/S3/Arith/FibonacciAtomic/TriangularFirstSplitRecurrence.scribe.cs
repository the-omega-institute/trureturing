using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class TriangularFirstSplitRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/TriangularFirstSplitRecurrence.";
    private static DocumentBlock Def(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(F.Id(name))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "No-split orbits and discounted first-split path values.",
        H("Triangular First-Split Values"), Blocks(
            Def("Path", "Arbitrary starting state", "A path starts at (r,e), uses the existing reduced triangular actions, and obeys legality and the successor equation at every natural depth. Its state bound is the initial retained label count e."),
            Def("rho", "No-split residual orbit", "The orbit starts at r and repeatedly sends a to 2a modulo e. This also retains the zero residual self-loop."),
            Def("J", "First visits", "The finite set consists of j less than e for which no earlier orbit index has the same residual. Thus it comprises all indices before the first repetition."),
            Def("U", "No-split cost", "The cost is the infinite real series summing rho(e,r,j)/2^j over all natural j."),
            Def("K", "No-split affine value", "Subtract x times r/e from U(e,r). Here x is any real price."),
            Def("pathValue", "Path objective", "The objective is the sum of residual layer counts divided by 2^d, minus x times the sum of anchor digits divided by 2^(d+1). The anchor digit and legal actions have their original meanings."),
            Def("W", "Infimum over paths", "Take the real infimum of the objectives of every infinite legal path from (r,e). Zero residual self-loops are included in this domain."),
            Def("splitChoices", "Finite positive split choices", "A pair (j,h) is retained precisely when j belongs to J(e,r), 2rho(e,r,j) is less than e, and 1 <= h <= 2rho(e,r,j)."),
            Def("corrections", "Discounted first-split corrections", "The set contains zero and, for every retained pair (j,h), the number [rho(e,r,j) + W(x,e-h,2rho(e,r,j)-h)/2 - K(x,e,rho(e,r,j))]/2^j."),
            Def("noSplitAction", "Action without positive splitting", "Choose the one action if e <= 2a, and otherwise choose zero(0)."),
            Def("noSplit", "Infinite no-split path", "For r < e, the states are (rho(e,r,j),e) and each action is the corresponding no-split action."),
            Def("suffix", "Path from a later state", "Discard the first n transitions. The initial state and the state bound are those of the original path at depth n."),
            Def("splitPath", "Path with a specified first split", "Follow the no-split path for j transitions, perform zero(h), and follow delta from the successor (2rho(e,r,j)-h,e-h). The parameters require r < e, 2rho(e,r,j) < e and h <= 2rho(e,r,j)."),
            Describe.Lean(DescribeId.Create("first-split-value"), DeclarationHandle.Create(Prefix + "result"),
                H("Finite first-split recurrence and attainment"), StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every natural m >= 2, every real price x, every retained count "
                        + "1 <= e <= m, and every natural residual r < e, W(x,e,0) is zero. "
                        + "If r is positive, W(x,e,r) equals K(x,e,r) plus the minimum of corrections(x,e,r). "
                        + "There exists an infinite legal path gamma from (r,e) whose objective equals W(x,e,r).")),
                    Paragraph(Text("The corrections set contains zero and the discounted correction "
                        + "[rho_j + W(x,e-h,2rho_j-h)/2 - K(x,e,rho_j)]/2^j for every first visit j "
                        + "with 2rho_j < e and every 1 <= h <= 2rho_j. Each positive split strictly "
                        + "reduces e, so the values on the right are obtained at smaller retained counts.")),
                    Paragraph(Text("Without a positive split, the residual follows the modular orbit, "
                        + "the cost is U(e,r), and the anchor mass is r/e. At the first positive split "
                        + "the common prefix cancels against this path, leaving the displayed correction. "
                        + "A later visit to the same residual has a smaller positive discount. A negative "
                        + "correction is therefore best at its first visit; a nonnegative correction "
                        + "cannot improve on zero. The finite minimum is attained by either the no-split "
                        + "path or a finite prefix, a split, and an attaining path at smaller e.")),
                    Paragraph(Text("The infimum ranges over all legal infinite paths. Finite candidate "
                        + "indices compute its value and one attaining path. They do not exclude later "
                        + "visits with zero correction, including arbitrary finite waits around a cycle."))),
                DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula Fn(string s, params Formula[] args) => Call(s, args);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Open, Forall, Sp, x, Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula And(Formula a, Formula b) =>
        Seq(Open, a, Sp, Land, Sp, b, Close);
    private static Formula Imp(Formula a, Formula b) =>
        Seq(Open, a, Sp, Implies, Sp, b, Close);

    private static Formula ResultFormula()
    {
        var m = V("m"); var e = V("e"); var r = V("r"); var x = V("x");
        var gamma = V("gamma"); var nat = Seq(Mathbb, Grp(V("N")));
        var real = Seq(Mathbb, Grp(V("R")));
        var zero = Equal(Fn("W", x, e, D(0)), D(0));
        var recurrence = Imp(Seq(D(0), Sp, Lt, Sp, r), Equal(Fn("W", x, e, r),
            Seq(Fn("K", x, e, r), Plus, Fn("min", Fn("corrections", x, e, r)))));
        var attained = Seq(Open, Exists, Sp, gamma, Colon, Sp, Fn("Path", e, r), Comma, Sp,
            Equal(Fn("pathValue", x, gamma), Fn("W", x, e, r)), Close);
        return Disp(All(m, nat, Imp(Seq(D(2), Sp, Le, Sp, m), All(x, real,
            All(e, nat, Imp(And(Seq(D(1), Sp, Le, Sp, e), Seq(e, Sp, Le, Sp, m)),
                All(r, nat, Imp(Seq(r, Sp, Lt, Sp, e), And(zero, And(recurrence, attained))))))))));
    }
}
