using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical;

internal sealed class SilverSlopeAbelianPellArithmeticDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/peltomaki2020abelianperiods");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pell approximation estimates and convergent-period constructions for the silver slope.",
        H("Silver Pell arithmetic and convergent periods"),
        Blocks(
            Node("pell-error-formula", "silverPell_error_formula", "The signed Pell error", Error(),
                "The error alternates in sign and its magnitude is the next power of the slope.", true),
            Node("pell-determinant", "silverPell_determinant", "The adjacent Pell determinant", Determinant(),
                "Consecutive denominators and numerators form a unimodular pair.", true),
            Node("best-approximation", "silver_best_approximation", "Smaller denominators have larger error", Best(),
                "Every positive denominator below q at index k+1 has error at least alpha to the power k+1.", true),
            Node("gap-approximation", "silver_gap_approximation", "The noncandidate approximation gap", Gap(),
                "Between successive Pell denominators, the three distinguished candidates are the only exceptions to the larger error bound.", false),
            Node("phase-mass", "silver_phase_mass", "The exact phase mass", Mass(),
                "The Pell recurrence and alpha squared plus twice alpha equals one give a constant phase mass.", false)), []));

    private static DocumentBlock Node(string id, string declaration, string title, Formula formula, string prose, bool literature) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S1/Words/Mechanical/SilverSlopeAbelianPellArithmetic." + declaration),
            H(title), StatementSource.FromAuthor(formula), literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose + " The operators real and integer denote canonical numeric coercions."))), DescribeRole.Theorem);
    private static Formula K => F.Id("k");
    private static Formula A => Call("silverSlope");
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Q(Formula k) => Call("P", Add(k, D(1)));
    private static Formula T(Formula k) => Call("P", k);
    private static Formula Next(Formula k, byte d) => Add(k, D(d));
    private static Formula R(Formula x) => Call("real", x);
    private static Formula I(Formula x) => Call("integer", x);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Ne(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.NotEqual, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Error() => Disp(All("k", N, Eq(Sub(Mul(R(Q(K)), A), R(T(K))),
        Mul(Pow(new Formula.Negate(D(1)), K), Pow(A, Next(K, 1))))));
    private static Formula Determinant() => Disp(All("k", N, Eq(Sub(Mul(I(Q(Next(K, 1))), I(T(K))), Pow(I(Q(K)), D(2))),
        Pow(new Formula.Negate(D(1)), Next(K, 1)))));
    private static Formula Best()
    {
        Formula m = F.Id("m"), z = F.Id("z");
        return Disp(All("k", N, All("m", N, All("z", new Formula.Integers(), Imp(And(Lt(D(0), m), Lt(m, Q(Next(K, 1)))),
            Le(Pow(A, Next(K, 1)), new Formula.Absolute(Sub(Mul(R(m), A), R(z)))))))));
    }
    private static Formula Gap()
    {
        Formula m = F.Id("m"), z = F.Id("z"), q = Q(Next(K, 1));
        Formula hypotheses = And(Le(q, m), And(Lt(m, Q(Next(K, 2))),
            And(Ne(m, q), And(Ne(m, Mul(D(2), q)), Ne(m, Add(q, Q(K)))))));
        return Disp(All("k", N, All("m", N, All("z", new Formula.Integers(), Imp(hypotheses,
            Le(Add(Pow(A, Next(K, 2)), Pow(A, Next(K, 1))), new Formula.Absolute(Sub(Mul(R(m), A), R(z)))))))));
    }
    private static Formula Mass() => Disp(All("k", N,
        Eq(Mul(Add(R(Q(Next(K, 1))), Mul(A, R(Q(K)))), Pow(A, Next(K, 1))), D(1))));
    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula>();
        for (int index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        return Seq(Operatorname, Grp(F.Id(name)), Parenthesized(Seq([.. items])));
    }
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);}
