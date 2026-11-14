using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class MatharA386830Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/MatharA386830.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceComposition/mathar2025a386830");
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, F.Id(name), Colon, type, Comma, Sp, body);
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Q => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula n => F.Id("n");
    private static Formula k => F.Id("k");
    private static Formula z => F.Id("z");
    private static Formula A(Formula index) => Call("a", index);
    private static Formula Sum(Formula index, Formula top, Formula term) => Seq(F.Sum, Underscore,
        Grp(Seq(index, Eq, D(0))), Caret, Grp(top), Sp, term);
    private static DocumentBlock Node(string name, string title, Formula statement, string prose, DescribeRole role, bool derived,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("mathar-a386830-" + name), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), derived ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    public DocumentDefinition Create()
    {
        var literal = Mul(Mul(Mul(Pow(D(3), k), Pow(D(2), Sub(n, k))),
            Call("choose", Add(Mul(D(3), n), D(1)), k)), Call("choose", Sub(Mul(D(3), n), k), Sub(n, k)));
        var leading = Mul(Mul(Mul(D(8), n), Sub(Mul(D(2), n), D(3))), A(n));
        var middle = Mul(Mul(D(6), Sub(Add(Mul(Seq(Minus, D(1, 0, 8)), Pow(n, D(2))),
            Mul(D(2, 0, 7), n)), D(8, 0))), A(Sub(n, D(1))));
        var trailing = Mul(Mul(Mul(D(4, 0, 5), Sub(Mul(D(3), n), D(2))),
            Sub(Mul(D(3), n), D(4))), A(Sub(n, D(2))));
        var recurrence = All("n", Nat, Seq(D(2), Sp, Le, Sp, n, Sp, Implies, Sp,
            Add(Add(leading, middle), trailing), Eq, D(0)));
        var r = F.Id("r");
        var j = F.Id("j");
        var dfinite = Seq(Exists, Sp, r, Colon, Nat, Comma, Sp, Exists, Sp, F.Id("p"), Colon,
            Seq(Nat, Sp, To, Sp, Q, OpenBracket, z, CloseBracket), Comma, Sp,
            Seq(Open, Exists, Sp, j, Colon, Nat, Comma, Sp, D(0), Sp, Le, Sp, j, Sp, Le, Sp, r,
                Sp, Land, Sp, Call("p", j), Sp, Neq, Sp, D(0), Close),
            Land, Sp, Sum(j, r, Mul(Call("p", j), Pow(F.Id("series"), Seq(Open, j, Close)))), Eq, D(0));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The literal inclusive integer sum A386830 satisfies Mathar's recurrence at every natural n>=2 and has a nonzero homogeneous ordinary formal differential operator.",
            H("Mathar's A386830 recurrence and ordinary D-finiteness"), Blocks(
            Paragraph(Text("The sequence is defined at every natural index, including zero. Both finite-sum endpoints are included. Binomial coefficients and exponents are natural, while the summands are integers. In the recurrence n is cast to the integers before coefficient subtraction; backshift indices remain natural under n>=2. The source has OFFSET 0,2 and states no onset: n>=2 is the adopted nonnegative-backshift interpretation, not an author-stated bound or the meaning of the second OFFSET component.")),
            Node("a", "Literal inclusive NAME sum", All("n", Nat, Seq(A(n), Eq, Sum(k, n, literal))),
                "This is Manyama's original NAME in OEIS A386830, revision 10. No other FORMULA equivalence is assumed.", DescribeRole.Definition, false),
            Node("series", "Entire ordinary rational formal series", Seq(F.Id("series"), Eq,
                Seq(F.Sum, Underscore, Grp(Seq(n, Eq, D(0))), Caret, Grp(Infty), Sp, Mul(A(n), Pow(z, n)))),
                "The coefficient at every natural index is the literal integer a(n), cast into Q. This is the entire ordinary Q[[z]] series, without an analytic convergence premise.", DescribeRole.Definition, true),
            Node("result", "Full recurrence and nonzero homogeneous operator", Seq(Open, recurrence, Close, Sp, Land, Sp, Open, dfinite, Close),
                "The first conjunct covers every natural n>=2. The second quantifies over polynomial coefficients indexed by the naturals and requires a nonzero member between 0 and r. The expression series superscript (j) denotes j-fold formal differentiation, with the zero-fold derivative equal to series, and each polynomial is embedded in Q[[z]]. An explicit order-three witness is p0=3240, p1=-588+25110z, p2=8-1998z+21870z squared, p3=16z-648z squared+3645z cubed. The constant p0 is nonzero. This is one conjunction from one source event, not two resolution credits; minimal order is not claimed.", DescribeRole.Theorem, true,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("mathar-a386830-recurrence-dfinite"), ResolutionKind.Proved)),
            Paragraph(Text("Expanding 5=3+2 and interchanging finite triangular sums reduces the original NAME to the alternating sum of 5 to the j times (-2) to the (n-j) times choose(3n+1,j). Nat.choose_mul and Int.alternating_sum_range_choose_eq_choose establish the equality for all n, including zero.")),
            Paragraph(Text("Three Pascal expansions and the finite geometric-sum identity give 4a(n)-27a(n-1)=9b(n) for all n>=1, where b(n)=5 to the n times choose(3n-2,n). Cross-multiplied adjacent-binomial identities give 2n(2n-3)b(n)=15(3n-2)(3n-4)b(n-1) for all n>=2. Eliminating b yields exactly the displayed integer recurrence, including its n=2 boundary.")),
            Paragraph(Text("Coefficient comparison proves the displayed homogeneous differential equation directly: the coefficient at index n is n+1 times the recurrence at n+2. Thus every coefficient vanishes, rather than a finite truncation. No EGF or negative-index extension is substituted.")),
            Paragraph(Text("Quoted source material is attributed to The Online Encyclopedia of Integer Sequences, https://oeis.org/A386830, under CC-BY-SA-4.0. Sequence: Seiichi Manyama, Aug 05 2025; conjecture: R. J. Mathar, Aug 19 2025. Worldwide solvedness and priority remain ASSUMED-UNVERIFIED beyond the bounded qualification in the library note.")))));
    }
}
