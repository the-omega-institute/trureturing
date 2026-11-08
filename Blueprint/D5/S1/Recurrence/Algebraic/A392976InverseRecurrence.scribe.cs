using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class A392976InverseRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/A392976InverseRecurrence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mathar2026a392976");
    private static Formula V(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Q => Seq(Mathbb, Grp(V("Q")));
    private static Formula PS => Seq(Q, OpenBracket, OpenBracket, V("X"), CloseBracket, CloseBracket);
    private static Formula Poly => Seq(Q, OpenBracket, V("X"), CloseBracket);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Pow(Formula f, long n) => new Formula.Power(f, Num(n));
    private static Formula Product(params Formula[] terms) => terms.Aggregate(Multiply);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Ne(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.NotEqual, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Fin(Formula d) => Call("Fin", Add(d, Num(1)));
    private static Formula Coeff(Formula n, Formula b) => Call("coeff", n, b);
    private static Formula Subst(Formula b, Formula c) => Call("subst", b, c);
    private static Formula Lag(long k) => Call("a", k == 0 ? V("n") : Subtract(V("n"), Num(k)));

    private static Formula Differential(Formula b)
    {
        Formula d = V("d");
        Formula j = V("j");
        Formula pj = Call("p", j);
        Formula sum = Seq(new Formula.Subscript(Sum, Seq(j, Colon, Fin(d))), Sp,
            Multiply(pj, Call("iterateDerivative", j, b)));
        return Some("d", Nat, Some("p", Seq(Fin(d), Sp, To, Sp, Poly),
            And(Some("j", Fin(d), Ne(pj, Num(0))), Equal(sum, Num(0)))));
    }

    private static Formula Recurrence()
    {
        Formula n = Call("castQ", V("n"));
        Formula n1 = Par(Subtract(n, Num(1)));
        Formula n2 = Par(Subtract(n, Num(2)));
        Formula first = Product(Num(283), n, n1, n2,
            Par(Subtract(Multiply(Num(83022305213), n), Num(178385058984))),
            Par(Add(n, Num(1))), Lag(0));
        Formula second = Product(Num(6), n, n1, n2,
            Par(Add(Subtract(Multiply(Num(12196786904129), Pow(n, 2)),
                Multiply(Num(45110300936020), n)), Num(52641391340361))), Lag(1));
        Formula third = Product(Num(6), n1, n2,
            Par(Add(Add(Subtract(Multiply(Num(67790996421377), Pow(n, 3)),
                Multiply(Num(248299346995054), Pow(n, 2))),
                Multiply(Num(202497447227007), n)), Num(3061418504418))), Lag(2));
        Formula fourth = Product(Num(2), n2,
            Par(Subtract(Add(Subtract(Subtract(Multiply(Num(192167357944360), Pow(n, 4)),
                Multiply(Num(559010679688491), Pow(n, 3))),
                Multiply(Num(2120668219560541), Pow(n, 2))),
                Multiply(Num(9123363136130610), n)), Num(8342981628089220))), Lag(3));
        Formula fifth = Product(Num(5),
            Par(Subtract(Add(Subtract(Add(Subtract(Multiply(Num(15640122296875), Pow(n, 5)),
                Multiply(Num(565964885220500), Pow(n, 4))),
                Multiply(Num(4989857715427325), Pow(n, 3))),
                Multiply(Num(18667678380008380), Pow(n, 2))),
                Multiply(Num(32085126156301848), n)), Num(20925325629575136))), Lag(4));
        Formula sixth = Product(Num(10),
            Par(Subtract(Multiply(Num(5), n), Num(17))),
            Par(Subtract(Multiply(Num(5), n), Num(18))),
            Par(Subtract(Multiply(Num(5), n), Num(21))),
            Par(Subtract(Multiply(Num(5), n), Num(19))),
            Par(Subtract(Multiply(Num(22509687685), n), Num(60308240636))), Lag(5));
        return All("n", Nat, Imp(Le(Num(5), V("n")),
            Equal(Add(Add(Subtract(Subtract(Subtract(first, second), third), fourth), fifth), sixth), Num(0))));
    }

    private static Formula FullClaim()
    {
        Formula u = V("U");
        Formula f = V("f");
        Formula x = V("X");
        Formula unique = All("V", PS, Imp(Equal(Coeff(Num(0), V("V")), Num(0)),
            Imp(Equal(Subst(f, V("V")), x), Equal(V("V"), u))));
        return And(Equal(Coeff(Num(0), u), Num(0)),
            And(Equal(Subst(f, u), x), And(Equal(Subst(u, f), x),
                And(unique, And(Equal(Multiply(x, V("A")), u),
                    And(Call("DFinite", V("A")), Recurrence()))))));
    }

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("a392976-" + (name == "A" ? "series" : name == "a" ? "sequence" : name.ToLowerInvariant())),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance ?? AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The inverse quintic satisfies the full A392976 recurrence and is D-finite.",
        H("A392976: The Formal Inverse Quintic Recurrence"), Blocks(
            Paragraph(Text("OEIS A392976, https://oeis.org/A392976, defines the sequence by reversion "
                + "of f(X)=X((1-X^2)^2-X). All series here are formal power series over Q, with "
                + "ordinary degree beginning at zero. Rational coefficients provide the characteristic-zero "
                + "carrier of the published integer sequence. The inverse has constant coefficient zero; "
                + "both formal compositions are X. No analytic branch is selected. The offset is zero. "
                + "The secondary offset three does not set the recurrence threshold. Every recurrence "
                + "index is a natural number at least five, representing every integer in that range, "
                + "and subtraction in a sequence argument is "
                + "natural subtraction. The function castQ embeds a natural number into Q. "
                + "Substitution uses the polynomial f as its formal power series.")),
            Paragraph(Text("The source is OEIS A392976, NAME and Mathar's FORMULA conjecture, "
                + "revision 19, January 31, 2026, pinned oeisdata export "
                + "4c6abcdf8b00fd262030066ebfced671457e5b43. The sequence is due to Seiichi Manyama; "
                + "the conjecture is due to R. J. Mathar, January 29, 2026. Credit The Online Encyclopedia "
                + "of Integer Sequences, the OEIS Foundation and the named contributors; the source text "
                + "is CC BY-SA 4.0. The Library note retains the literal source wording and immutable locator. "
                + "The author gives no onset: n at least five is the valid-lag interpretation, not a quotation.")),
            Node("f", "The quintic polynomial",
                Equal(V("f"), Multiply(V("X"), Par(Subtract(Pow(Par(Subtract(Num(1), Pow(V("X"), 2))), 2), V("X"))))),
                "The polynomial lies in Q[X], has constant coefficient zero and linear coefficient one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("U", "The zero-constant inverse",
                Equal(V("U"), Call("substInvOfIsUnit", V("f"))),
                "The formal inverse construction applies because the linear coefficient of f is a unit. "
                    + "Its defining uniqueness and both inverse compositions appear in the complete assertion below.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("A", "The quotient series",
                Equal(V("A"), Call("mk", Par(Seq(V("n"), Colon, Nat, Sp, Mapsto, Sp,
                    Coeff(Add(V("n"), Num(1)), V("U")))))),
                "The n-th coefficient is the coefficient of degree n+1 in U, so X A=U.",
                DescribeRole.Definition),
            Node("a", "The offset-zero sequence",
                All("n", Nat, Equal(Call("a", V("n")), Coeff(Add(V("n"), Num(1)), V("U")))),
                "Thus A is the ordinary generating series of a(n), beginning at n=0.", DescribeRole.Definition),
            Node("DFinite", "Homogeneous D-finiteness",
                All("B", PS, new Formula.Logic(Call("DFinite", V("B")), FormulaLogicOperator.Iff, Differential(V("B")))),
                "The derivative is formal. A polynomial family indexed by Fin(d+1) gives the coefficients "
                    + "of derivative orders zero through d. At least one polynomial is nonzero; "
                    + "the differential equation is homogeneous.", DescribeRole.Definition),
            Node("claim", "The complete inverse and recurrence assertion",
                new Formula.Logic(V("claim"), FormulaLogicOperator.Iff, FullClaim()),
                "The assertion includes both inverse compositions, uniqueness among all zero-constant "
                    + "formal right inverses, X A=U, homogeneous D-finiteness, and all six signed terms "
                    + "of the stated recurrence at every n at least five. No exceptional index is removed.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The full A392976 identity and D-finiteness", FullClaim(),
                "Write theta=X d/dX and let c(k,n) be the six signed polynomial coefficients displayed above. "
                    + "The operator sum over k=0,...,5 of X^k c(k,theta+k) annihilates A. Multiplication "
                    + "by X transforms it into the corresponding operator on U with theta+k-1. "
                    + "After composition with f, the chain rule clears denominators using H=f', "
                    + "whose constant coefficient is one. The resulting polynomial identity is zero. "
                    + "Coefficient extraction gives exactly the displayed identity at every n at least five. "
                    + "Expanding theta powers into ordinary derivatives gives a homogeneous operator of "
                    + "order five; its fifth-derivative polynomial has coefficient 23495312375279 at degree five, "
                    + "so the operator is nonzero. No minimal-order assertion is made.",
                DescribeRole.Theorem, resolution: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a392976-inverse-recurrence"), ResolutionKind.Proved)))));
}
