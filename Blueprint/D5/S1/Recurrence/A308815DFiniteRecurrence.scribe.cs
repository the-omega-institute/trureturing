using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class A308815DFiniteRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/A308815DFiniteRecurrence.";
    private static readonly LibraryNoteRef Oeis =
        LibraryNoteRef.Create("D5/L/Words/mathar2020a308815");
    private static readonly LibraryNoteRef Paper =
        LibraryNoteRef.Create("D5/L/Geometry/farkas2021alternating");

    private static Formula N => F.Id("n");
    private static Formula Z => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Pow(Formula f, Formula e) => new Formula.Power(f, e);
    private static Formula Cast(Formula f) => Parenthesized(Seq(f, Colon, Z));
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(owner)), Dot,
            Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula A(Formula n) => Call("a308815", n);
    private static Formula Lag(int k) => A(Subtract(N, Num(k)));
    private static Formula Product(params Formula[] fs) =>
        fs.Aggregate(Multiply);

    private static Formula Sequence()
    {
        Formula i = F.Id("i");
        Formula range = Qualified("Finset", "range", Add(N, Num(1)));
        Formula sum = Seq(new Formula.Subscript(Sum,
            Seq(i, Sp, InMacro, Sp, range)), Sp,
            Product(Pow(Cast(Seq(Minus, Num(2))), i),
                Cast(Qualified("Nat", "choose", N, i)),
                Cast(Call("catalan", Subtract(Multiply(Num(2), N), i)))));
        return Disp(All(Equal(A(N), Multiply(Pow(Num(16), N), sum))));
    }

    private static Formula All(Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"), Nat, body);

    private static Formula Recurrence()
    {
        Formula z = Cast(N);
        Formula first = Product(z, Parenthesized(Add(Multiply(Num(2), z), Num(1))), A(N));
        Formula second = Product(Num(32),
            Parenthesized(Subtract(Multiply(Num(9), z), Num(4))),
            Parenthesized(Subtract(z, Num(1))), Lag(1));
        Formula third = Product(Num(1024), Parenthesized(Add(
            Subtract(Multiply(Num(3), Pow(z, Num(2))), Multiply(Num(23), z)), Num(29))), Lag(2));
        Formula fourth = Product(Num(65536), Parenthesized(Subtract(z, Num(2))),
            Parenthesized(Subtract(Multiply(Num(2), z), Num(5))), Lag(3));
        Formula equation = Equal(Add(Add(Subtract(first, second), third), fourth), Num(0));
        return All(new Formula.Logic(
            new Formula.Relation(Num(3), FormulaRelationOperator.LessThanOrEqual, N),
            FormulaLogicOperator.Implies, equation));
    }

    private static DocumentBlock Node(string name, string title, Formula formula,
        AssessedProvenance provenance, string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("a308815-" + name),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mathar's D-finite recurrence for the alternating Catalan numbers.",
        H("The alternating Catalan recurrence"),
        Blocks(
            Paragraph(Text("The sequence is the signed binomial transform of the Catalan numbers, "
                + "scaled by 16 to the index power. All sum indices and sequence arguments are natural "
                + "numbers; subtraction in an argument, including 2n-i, is natural truncated subtraction. "
                + "Every polynomial coefficient of the recurrence is evaluated in the integers. "
                + "The parenthesized casts to Z display that distinction.")),
            Node("a308815", "Alternating Catalan numbers", Sequence(),
                AssessedProvenance.FromLiterature(Paper),
                "Theorem 1.1, page 1 of arXiv:1906.10406v2: “The number of odd covers of degree "
                + "2g + 1 of a general curve of genus g ≥ 3 equals” the displayed signed binomial sum. "
                + "The genus g is n here, and Mathlib's catalan is the ordinary Catalan sequence. "
                + "OEIS A308815 gives the same expression in its PARI program: "
                + "“a(n) = 16^n*sum(i=0, n, (-2)^i*binomial(n, i)*C(2*n-i));”. "
                + "The NAME line prints 2^i; the PARI expression and the displayed data use (-2)^i. "
                + "The sum defines the initial indices as well; the geometric interpretation starts at n ≥ 3.",
                DescribeRole.Definition),
            Node("claim", "Mathar's recurrence assertion",
                Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Recurrence())),
                AssessedProvenance.FromLiterature(Oeis),
                "OEIS A308815, FORMULA section (no page numbers): “Conjecture: D-finite with recurrence: "
                + "n*(2*n+1)*a(n) -32*(9*n-4)*(n-1)*a(n-1) +1024*(3*n^2-23*n+29)*a(n-2) "
                + "+65536*(n-2)*(2*n-5)*a(n-3)=0. - _R. J. Mathar_, Jan 27 2020”. "
                + "Here a is a308815. The assertion ranges over every natural n ≥ 3; lagged indices "
                + "use natural subtraction, and the factors n-1 and n-2 outside a308815 use integer subtraction.",
                DescribeRole.Definition),
            Node("result", "The recurrence holds", Disp(Recurrence()),
                AssessedProvenance.FromRepo(Oeis),
                "The ordinary Catalan series satisfies X C(X)^2-C(X)+1=0. Differentiation and elimination "
                + "give X(1-4X)C'(X)+(1-2X)C(X)=1. The signed binomial sum is the coefficient "
                + "of degree 2n in (1-2X)^n C(X). For n=m+3, the differential certificate "
                + "X U'(X)-2(m+3)U(X) is a polynomial combination of the four shifted coefficient expressions, "
                + "plus a forcing polynomial of degree at most m+5. Its degree-2(m+3) coefficient is zero: "
                + "the Euler derivative cancels that coefficient, and m+5 < 2(m+3). Extracting coefficients "
                + "and multiplying by 16^(m+3) produces the stated integer recurrence. "
                + "The generating-function closed form and asymptotic formula are not proved by this module.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a308815-dfinite-recurrence"),
                    ResolutionKind.Proved)))));
}
