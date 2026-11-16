using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class MatharA386844Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/MatharA386844.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/AnalyticClosure/mathar2026a386844");
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, int b) => new Formula.Power(a, Num(b));
    private static Formula Num(int value) => D(value.ToString(System.Globalization.CultureInfo.InvariantCulture).Select(c => (byte)(c - '0')).ToArray());
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, F.Id(name), Colon, type, Comma, Sp, body);
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Q => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula n => F.Id("n");
    private static Formula z => F.Id("z");
    private static Formula Aval(Formula index) => Call("a", index);
    private static Formula IntAval(Formula index) => Seq(Open, Aval(index), Colon, Mathbb, Grp(F.Id("Z")), Close);
    private static Formula Rval(int order, Formula index) => Seq(F.Id("R"), Underscore, Grp(Num(order)), Open, index, Close);
    private static Formula Sum(Formula index, Formula top, Formula term) => Seq(F.Sum, Underscore,
        Grp(Seq(index, Eq, D(0))), Caret, Grp(top), Sp, term);
    private static DocumentBlock Node(string name, string title, Formula statement, string prose,
        DescribeRole role = DescribeRole.Definition, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("mathar-a386844-" + (name == "A" ? "ordinary-series" : name.ToLowerInvariant())), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)),
            name is "a" or "R3" or "R2" ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    public DocumentDefinition Create()
    {
        var k = F.Id("k");
        var r = F.Id("r");
        var j = F.Id("j");
        var p = F.Id("p");
        var f = F.Id("f");
        var seriesType = Seq(Q, OpenBracket, OpenBracket, z, CloseBracket, CloseBracket);
        var polyType = Seq(Q, OpenBracket, z, CloseBracket);
        var literal = Mul(Call("choose", Add(Mul(D(3), n), D(2)), k), Call("choose", Sub(Mul(D(3), n), k), Sub(n, k)));
        var m = Seq(Open, n, Colon, Mathbb, Grp(F.Id("Z")), Close);
        var rthree = Sub(Add(Add(Mul(Mul(Mul(D(3), m), Sub(Mul(D(2), m), D(1))), IntAval(n)),
            Mul(Sub(Add(Sub(D(0), Mul(Num(353), Pow(m, 2))), Mul(Num(1009), m)), Num(672)), IntAval(Sub(n, D(1))))),
            Mul(Add(Sub(Mul(Num(3938), Pow(m, 2)), Mul(Num(15029), m)), Num(13872)), IntAval(Sub(n, D(2))))),
            Mul(Mul(Mul(Num(399), Sub(Mul(D(3), m), D(4))), Sub(Mul(D(3), m), D(5))), IntAval(Sub(n, D(3)))));
        var rtwo = Add(Add(Mul(Mul(Mul(m, Sub(Mul(D(2), m), D(1))), Sub(Mul(D(5), m), D(8))), IntAval(n)),
            Mul(Add(Sub(Add(Sub(D(0), Mul(Num(145), Pow(m, 3))), Mul(Num(362), Pow(m, 2))), Mul(Num(264), m)), Num(63)), IntAval(Sub(n, D(1))))),
            Mul(Mul(Mul(Mul(D(3), Sub(Mul(D(3), m), D(1))), Sub(Mul(D(5), m), D(3))), Sub(Mul(D(3), m), D(2))), IntAval(Sub(n, D(2)))));
        var finitePolys = Seq(Call("Fin", Add(r, D(1))), Sp, To, Sp, polyType);
        var nonzero = Seq(Exists, Sp, j, Colon, Call("Fin", Add(r, D(1))), Comma, Sp, Call("p", j), Sp, Neq, Sp, D(0));
        var dfinite = Seq(Exists, Sp, r, Colon, Nat, Comma, Sp, Exists, Sp, p, Colon, finitePolys, Comma, Sp,
            Open, nonzero, Close, Sp, Land, Sp, Call("op", r, p, F.Id("A")), Eq, D(0));
        var recThree = All("n", Nat, Seq(D(3), Sp, Le, Sp, n, Sp, Implies, Sp, Rval(3, n), Eq, D(0)));
        var recTwo = All("n", Nat, Seq(D(2), Sp, Le, Sp, n, Sp, Implies, Sp, Rval(2, n), Eq, D(0)));
        var whole = Seq(Open, recThree, Close, Sp, Land, Sp,
            Open, recTwo, Close, Sp, Land, Sp, Open, dfinite, Close);
        return DocumentDefinition.Create(ScribeNode.Create(
            "The native A386844 binomial sum, both guarded signed recurrences, and ordinary formal D-finiteness.",
            H("Mathar's A386844 twin recurrence problem"), Blocks(
            Paragraph(Text("The sequence is the inclusive natural binomial sum in OEIS A386844. The two recurrences are Mathar's conjectures in revision 16. Their starting indices 3 and 2 are the natural-lag interpretations: both endpoints are included. Every polynomial and signed recurrence operation is evaluated in the integers after casting n and a(n); only the lag indices use natural subtraction.")),
            Node("a", "Literal native sequence", All("n", Nat, Seq(Aval(n), Eq, Sum(k, n, literal))),
                "Both k=0 and k=n are included, and n ranges over all natural numbers including zero. The values a(n) are natural numbers."),
            Node("R3", "Third lag signed expression", All("n", Nat, Seq(Rval(3, n), Eq, rthree)),
                "The expression is integer valued. The recurrence asserts its vanishing only for n>=3, including 3."),
            Node("R2", "Second lag signed expression", All("n", Nat, Seq(Rval(2, n), Eq, rtwo)),
                "The expression is integer valued. The recurrence asserts its vanishing only for n>=2, including 2."),
            Node("A", "Complete ordinary series", Seq(F.Id("A"), Eq, Seq(F.Sum, Underscore, Grp(Seq(n, Eq, D(0))), Caret, Grp(Infty), Sp, Mul(Seq(Open, Aval(n), Colon, Q, Close), new Formula.Power(z, n)))),
                "A belongs to Q[[z]] and has rational coefficient a(n) at every natural index. It is an ordinary formal power series, with no convergence assumption."),
            Node("D", "Iterated formal derivative", All("j", Nat, All("f", seriesType, Seq(Call("D", j, f), Eq,
                Seq(new Formula.Power(F.Id("derivative"), j), Open, f, Close)))),
                "The superscript on derivative denotes function iteration. D(0,f)=f."),
            Node("op", "Finite polynomial differential operator", All("r", Nat, All("p", finitePolys, All("f", seriesType,
                Seq(Call("op", r, p, f), Eq, Sum(j, r, Mul(Call("p", j), Call("D", j, f))))))),
                "The sum uses all finite indices j from zero through r. Each polynomial is embedded into Q[[z]] before multiplication."),
            Node("P", "Exact whole conjunction", Seq(F.Id("P"), Iff, Sp, whole),
                "P requires both universal signed recurrences and a finite nonzero homogeneous polynomial differential operator on this same complete A."),
            Node("result", "Both recurrences and ordinary D-finiteness", whole,
                "The literal coefficient identity identifies A with (1+w)^3/(1-5w), where w has zero constant term and z(1+w)^3=w(1-w)^2. Lagrange substitution supplies this all-index bridge. The transported numerator identities give O3 A=8z+532z^2 and O2 A=-8z. Coefficient extraction gives the stated guarded recurrences, including their endpoints. Applying theta-1 to the second forcing identity and cancelling z^2 gives the ordinary differential operator with coefficients 420; 3612z-177; 4593z^2-1209z+6; 1539z^3-943z^2+29z; 135z^4-145z^3+10z^2. Its constant coefficient polynomial 420 is nonzero. All substitutions and derivatives are formal.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("mathar-a386844-twin-recurrences-dfinite"), ResolutionKind.Proved)),
            Paragraph(Text("The order-four operator is a witness to D-finiteness; no minimality or analytic convergence is asserted. Revision 16 supplies the two conjectured recurrence formulas but does not specify their onsets. The domains n>=3 and n>=2 are the natural-lag interpretations used here. The source and bounded literature scope are recorded in the Library note and matching Problems dossier; worldwide openness and priority remain unverified.")))));
    }
}
