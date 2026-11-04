using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.YoungFibonacci;

internal sealed class PetrovScottAltQCharlierPositivityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/YoungFibonacci/PetrovScottAltQCharlierPositivity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/petrovscott2026clone");
    private const string RecursionQuote =
        "For any Fibonacci word w, define the (biserial) clone Schur function s_w(x⃗ | y⃗) "
        + "through the following recurrence: s_w(x⃗ | y⃗) := A_k(x⃗ | y⃗), if w = 1^k for some k ≥ 0; "
        + "B_k(x⃗ + |u| | y⃗ + |u|) · s_u(x⃗ | y⃗), if w = 1^k2u for some k ≥ 0.";
    private const string PositiveQuote =
        "If s_w(x⃗ | y⃗) > 0 for all w ∈ 𝕐𝔽, we say that (x⃗, y⃗) is Fibonacci positive.";
    private const string ClaimQuote =
        "There exist values of ρ and q for which the following specialization (which we "
        + "call the alternative q-Charlier) is Fibonacci positive:";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Alternative q-Charlier Fibonacci positivity at rho = q = 1/4.",
        H("Alternative q-Charlier Fibonacci Positivity"),
        Blocks(
            Node("A", "The first tridiagonal determinant", DeterminantFormula(false),
                "Define two sequences of tridiagonal determinants as follows: (arXiv:2412.21126v2, "
                + "p. 15, equation (2.10)). A is the determinant with diagonal x at indices 1 through ell, "
                + "upper diagonal y and lower diagonal one. The displayed Matrix.of gives every entry, "
                + "including zero outside these three diagonals. The empty determinant is one.",
                AssessedProvenance.FromLiterature(Source)),
            Node("B", "The second tridiagonal determinant", DeterminantFormula(true),
                "Define two sequences of tridiagonal determinants as follows: (arXiv:2412.21126v2, "
                + "p. 15, equation (2.10)). B k has size k+1; its first row starts with y 1 and x 1 times y 2. "
                + "The remaining diagonal starts at x 3, its upper diagonal at y 3, and its lower diagonal is one.",
                AssessedProvenance.FromLiterature(Source)),
            Node("sAux", "Recursion with leading ones", AuxFormula(),
                RecursionQuote + " (Definition 2.5, p. 15). The auxiliary recursion counts k initial letters one. "
                + "At an empty tail it returns A k; "
                + "a letter one increases k; every other letter contributes B k with sequences shifted by "
                + "the sum of the remaining letters, followed by the recursion at zero. Only letters one "
                + "and two occur in Fibonacci words.", AssessedProvenance.FromLiterature(Source)),
            Node("s", "Biserial clone Schur functions", SchurFormula(),
                RecursionQuote + " (Definition 2.5, p. 15). Fibonacci words are lists over {1, 2}; "
                + "the weight |u| is List.sum u. The function s starts sAux with zero initial letters one.",
                AssessedProvenance.FromLiterature(Source)),
            Node("FibonacciPositive", "Fibonacci positivity", PositiveFormula(),
                PositiveQuote + " (Definition 4.1, p. 21). The real sequences are indexed from one. "
                + "The implication restricts the list to letters one and two, and includes the empty word.",
                AssessedProvenance.FromLiterature(Source)),
            Node("xAQC", "The alternative q-Charlier x sequence", SpecializationFormula(false),
                ClaimQuote + " (Conjecture 6.3, p. 31). This is its printed x expression. "
                + "The sequence is used for k ≥ 1; its extension at zero is immaterial. "
                + "Each exponent is an integer, so the negative exponents at k=1 are retained.",
                AssessedProvenance.FromLiterature(Source)),
            Node("yAQC", "The alternative q-Charlier y sequence", SpecializationFormula(true),
                ClaimQuote + " (Conjecture 6.3, p. 31). This is its printed y expression, used for k ≥ 1. "
                + "The casts from natural k to Int and every denominator factor are displayed.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Petrov–Scott Conjecture 6.3",
                Disp(Iff(F.Id("claim"), Parenthesized(ClaimBody()))),
                ClaimQuote + " (Conjecture 6.3, p. 31). The specialization is xAQC and yAQC above. "
                + "Both existential parameters range over Real, and positivity quantifies over every Fibonacci word.",
                AssessedProvenance.FromLiterature(Source)),
            Node("det_pos_of_dominant", "Positive determinant from diagonal dominance",
                DominantDeterminantFormula(),
                "A real matrix with positive diagonal entries and strict row diagonal dominance "
                + "has positive determinant.", AssessedProvenance.FromRepo(), DescribeRole.Theorem),
            Node("result", "Positivity at rho = q = one quarter", Disp(ClaimBody()),
                "Take rho=q=1/4. A positive diagonal rescaling turns the tridiagonal determinants "
                + "into strictly diagonally dominant matrices. The normalized sequence is nonnegative, "
                + "at most 1/4, positive at positive indices, and, from index one onward, "
                + "contracts by a factor at most 1/2. "
                + "A continuous deformation to the diagonal matrix preserves nonsingularity and hence "
                + "the positive determinant sign. Induction on the list then proves positivity for "
                + "every Fibonacci word, with no bound on its weight.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("petrov-scott-2026-alternative-q-charlier-fibonacci-positivity-conjecture-6-3"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("petrov-scott-qcharlier-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula DominantDeterminantFormula()
    {
        Formula index = Iota, matrix = F.Id("M"), i = F.Id("i"), j = F.Id("j");
        Formula diagonal = All([B("i", index)], Lt(D(0), App(matrix, i, i)));
        Formula offDiagonal = App(Q("Finset", "sum"),
            App(Q("Finset", "erase"), Q("Finset", "univ"), i),
            Lambda("j", index, Seq(Vert, Sp, App(matrix, i, j), Sp, Vert)));
        Formula dominance = All([B("i", index)], Lt(offDiagonal, App(matrix, i, i)));
        Formula body = All([B("M", Call("Matrix", index, index, Real()))],
            Implies(diagonal, Implies(dominance, Lt(D(0), App(Q("Matrix", "det"), matrix)))));
        body = Seq(OpenBracket, Call("Fintype", index), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", index), CloseBracket, Sp, body);
        return Disp(Seq(Forall, Sp, Cast(index, F.Id("Type")), Comma, Sp, body));
    }

    private static Formula DeterminantFormula(bool second)
    {
        Formula x = F.Id("x"), y = F.Id("y"), n = F.Id("n"), i = F.Id("i"), j = F.Id("j");
        Formula size = second ? Add(n, D(1)) : n;
        Formula entry = If(Equal(Cast(i, Nat()), Cast(j, Nat())), Call("x", Add(Cast(i, Nat()), second ? D(2) : D(1))),
            If(Equal(Cast(j, Nat()), Add(Cast(i, Nat()), D(1))), Call("y", Add(Cast(i, Nat()), second ? D(2) : D(1))),
                If(Equal(Cast(i, Nat()), Add(Cast(j, Nat()), D(1))), D(1), D(0))));
        if (second)
            entry = If(And(Equal(Cast(i, Nat()), D(0)), Equal(Cast(j, Nat()), D(0))), Call("y", D(1)),
                If(And(Equal(Cast(i, Nat()), D(0)), Equal(Cast(j, Nat()), D(1))),
                    Multiply(Call("x", D(1)), Call("y", D(2))), entry));
        Formula matrix = App(Q("Matrix", "of"), Lambda("i", Call("Fin", size),
            Lambda("j", Call("Fin", size), entry)));
        return Disp(All([B("x", SequenceType()), B("y", SequenceType()), B("n", Nat())],
            Equal(Call(second ? "B" : "A", x, y, n), App(Q("Matrix", "det"), matrix))));
    }

    private static Formula AuxFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y"), k = F.Id("k"), w = F.Id("w"), a = F.Id("a"), u = F.Id("u");
        Formula sum = App(Q("List", "sum"), u);
        Formula shiftedX = Lambda("j", Nat(), Call("x", Add(F.Id("j"), sum)));
        Formula shiftedY = Lambda("j", Nat(), Call("y", Add(F.Id("j"), sum)));
        Formula EmptyCase() => All([B("x", SequenceType()), B("y", SequenceType()), B("k", Nat())],
            Equal(Call("sAux", x, y, k, Q("List", "nil")), Call("A", x, y, k)));
        Formula OnesCase() => All([B("x", SequenceType()), B("y", SequenceType()), B("k", Nat()), B("w", ListType())],
            Equal(Call("sAux", x, y, k, App(Q("List", "cons"), D(1), w)), Call("sAux", x, y, Add(k, D(1)), w)));
        Formula OtherCase() => All([B("x", SequenceType()), B("y", SequenceType()), B("k", Nat()), B("a", Nat()), B("u", ListType())],
            Implies(new Formula.Relation(a, FormulaRelationOperator.NotEqual, D(1)),
                Equal(Call("sAux", x, y, k, App(Q("List", "cons"), a, u)),
                    Multiply(Call("B", shiftedX, shiftedY, k), Call("sAux", x, y, D(0), u)))));
        return Disp(new Formula.Aligned([EmptyCase(), OnesCase(), OtherCase()]));
    }

    private static Formula SchurFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y"), w = F.Id("w");
        return Disp(All([B("x", SequenceType()), B("y", SequenceType()), B("w", ListType())],
            Equal(Call("s", x, y, w), Call("sAux", x, y, D(0), w))));
    }

    private static Formula PositiveFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y"), w = F.Id("w"), a = F.Id("a");
        Formula letters = All([B("a", Nat())], Implies(
            new Formula.Relation(a, FormulaRelationOperator.MemberOf, w), Or(Equal(a, D(1)), Equal(a, D(2)))));
        Formula body = All([B("w", ListType())], Implies(letters, Lt(D(0), Call("s", x, y, w))));
        return Disp(All([B("x", SequenceType()), B("y", SequenceType())],
            Iff(Call("FibonacciPositive", x, y), Parenthesized(body))));
    }

    private static Formula SpecializationFormula(bool second)
    {
        Formula rho = F.Id("rho"), q = F.Id("q"), k = F.Id("k");
        Formula z = Cast(k, F.Id("Int"));
        Formula Pow(Formula e) => new Formula.Power(q, e);
        Formula TwiceMinus(byte a) => Subtract(Multiply(D(2), z), D(a));
        Formula Factor(Formula e) => Parenthesized(Add(D(1), Multiply(rho, Pow(e))));
        Formula numerator = second
            ? Multiply(Multiply(Multiply(rho, Pow(Subtract(Multiply(D(3), z), D(2)))),
                Parenthesized(Subtract(D(1), Pow(z)))), Factor(Subtract(z, D(1))))
            : Multiply(Pow(Subtract(z, D(1))), Parenthesized(Subtract(
                Add(Add(D(1), Multiply(rho, Pow(Subtract(z, D(2))))), Multiply(rho, Pow(Subtract(z, D(1))))),
                Multiply(rho, Pow(TwiceMinus(2))))));
        Formula denominator = second
            ? Multiply(Multiply(Factor(Multiply(D(2), z)), new Formula.Power(Factor(TwiceMinus(1)), D(2))), Factor(TwiceMinus(2)))
            : Multiply(Factor(TwiceMinus(3)), Factor(TwiceMinus(1)));
        return Disp(All([B("rho", Real()), B("q", Real()), B("k", Nat())],
            Equal(Call(second ? "yAQC" : "xAQC", rho, q, k), new Formula.Fraction(numerator, denominator))));
    }

    private static Formula ClaimBody() => new Formula.BindMany(FormulaQuantifier.Exists,
        [B("rho", Real()), B("q", Real())],
        Call("FibonacciPositive", Call("xAQC", F.Id("rho"), F.Id("q")), Call("yAQC", F.Id("rho"), F.Id("q"))));

    private static Formula Nat() => F.Id("Nat");
    private static Formula Real() => F.Id("Real");
    private static Formula SequenceType() => new Formula.TypeArrow(Nat(), Real());
    private static Formula ListType() => App(F.Id("List"), Nat());
    private static Formula.BoundVariable B(string name, Formula type) => new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula.BoundVariable[] variables, Formula body) => new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(F.Id(name), args);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula Lambda(string name, Formula type, Formula body) => Parenthesized(Seq(F.Id("fun"), Sp,
        Cast(F.Id(name), type), Sp, Mapsto, Sp, body));
    private static Formula If(Formula condition, Formula yes, Formula no) => Parenthesized(Seq(F.Id("if"), Sp,
        Parenthesized(condition), Sp, F.Id("then"), Sp, yes, Sp, F.Id("else"), Sp, no));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Lt(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
}
