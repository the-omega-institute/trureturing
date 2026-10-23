using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class PositiveFourierApproximationRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Fourier/PositiveFourierApproximationRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/herrera2023functionapproximation");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive-Fourier defect dilation and a three-point certificate refute Herrera's operator-monotone function-approximation conjecture.",
        H("Refutation of Herrera's function-approximation conjecture"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("is-admissible"),
                DeclarationHandle.Create(Prefix + "IsAdmissible"),
                H("Admissible positive-Fourier approximants"),
                StatementSource.FromAuthor(Disp(IsAdmissibleFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The admissible class is the source's C1 functions whose derivative is the Fourier transform of a finite positive Borel measure; the integral uses the stated complex exponential convention."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("approx-cost"),
                DeclarationHandle.Create(Prefix + "approxCost"),
                H("Approximation cost"),
                StatementSource.FromAuthor(Disp(ApproxCostFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The cost is the oscillation of f-g on the nonnegative half-line plus c times the derivative at zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("approx-error"),
                DeclarationHandle.Create(Prefix + "approxError"),
                H("Function-approximation functional"),
                StatementSource.FromAuthor(Disp(ApproxErrorFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The infimum ranges over admissible g for which the approximation error has bounded upper and lower ranges."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("operator-monotone-on"),
                DeclarationHandle.Create(Prefix + "OperatorMonotoneOn"),
                H("Operator monotonicity on positive semidefinite matrices"),
                StatementSource.FromAuthor(Disp(OperatorMonotoneFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The matrix order condition is imposed at every finite dimension for positive semidefinite A and B."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Herrera's Conjecture 2"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The source sentence is verbatim (arXiv v1, p. 7): “Let f be a non-negative function that is operator monotone on [0, ∞). Then E_f(c) ≤ Cf(c) holds for all c > 0 when C = 1.” This is Conjecture 2, numbered 1.10 in print; the formula binds the Lean encoding of f, operator monotonicity, c and positivity."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The conjecture is refuted"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The witness is f(x)=x/(1+x) at c=1. Positive Fourier structure gives a cubic defect-dilation bound, and the three-point comparison forces every admissible approximant to have cost at least 1153/2304, while f(1)=1/2. The function is nonnegative and operator monotone by the resolvent formula.")),
                    Paragraph(Text(
                        "The source's bound C<1.01975 remains an upper bound for this function. The optimal constant is open between 1153/1152 and 1.01975; the paper's commutator Conjectures 1 and 3 remain open because the implication from Conjecture 2 is not reversible."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("herrera-2023-function-approximation-conjecture"),
                    ResolutionKind.Refuted)))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Real() => Seq(Mathbb, Grp(Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(Id("C")));
    private static Formula Nat() => Seq(Mathbb, Grp(Id("N")));
    private static Formula Matrix(Formula n) => Call("Matrix", Call("Fin", n), Call("Fin", n), Complex());
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Qualified(string owner, string name) =>
        Seq(Id(owner), Dot, Id(name));
    private static Formula Call(string name, params Formula[] args)
    {
        Formula head = name switch
        {
            "Set.Ici" => Qualified("Set", "Ici"),
            "Set.range" => Qualified("Set", "range"),
            "Matrix.PosSemidef" => Qualified("Matrix", "PosSemidef"),
            "Complex.exp" => Qualified("Complex", "exp"),
            "Complex.I" => Qualified("Complex", "I"),
            "LE.le" => Qualified("LE", "le"),
            "LT.lt" => Qualified("LT", "lt"),
            _ => Id(name)
        };
        return new Formula.Apply(head, [.. args]);
    }
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula Arrow(Formula left, Formula right) => new Formula.TypeArrow(left, right);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula And(params Formula[] values) =>
        Seq(values.SelectMany((value, index) => index == 0
            ? new[] { Parenthesized(value) }
            : new[] { Land, Sp, Parenthesized(value) }).ToArray());
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Parenthesized(Seq(Id(name), Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula Ici() => Call("Set.Ici", Cast(D(0), Real()));
    private static Formula Function(Formula domain, Formula codomain) => Arrow(domain, codomain);

    private static Formula IsAdmissibleFormula()
    {
        var g = Id("g");
        var x = Id("x");
        var t = Id("t");
        var measure = Call("Measure", Real());
        var body = And(
            Call("ContDiff", Real(), D(1), g),
            Some("mu", measure,
                And(Call("IsFiniteMeasure", Id("mu")),
                    All("x", Real(), Eq(Cast(Call("deriv", g, x), Complex()),
                        Call("integral",
                            Lambda("t", Real(),
                                Call("Complex.exp", Negate(Mul(
                                    Mul(Cast(t, Complex()), Cast(x, Complex())),
                                    Qualified("Complex", "I"))))),
                            Id("mu")))))));
        return All("g", Function(Real(), Real()), Iff(Call("IsAdmissible", g), body));
    }

    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, type));
    private static Formula Negate(Formula value) => Seq(Minus, value);

    private static Formula ApproxCostFormula()
    {
        var f = Id("f");
        var g = Id("g");
        var c = Id("c");
        var x = Id("x");
        var residual = Sub(Call("f", Call("val", x)), Call("g", Call("val", x)));
        var sup = Call("iSup", Lambda("x", Ici(), residual));
        var inf = Call("iInf", Lambda("x", Ici(), residual));
        var equation = Eq(Call("approxCost", f, g, c),
            Add(Sub(sup, inf), Mul(c, Call("deriv", g, D(0)))));
        return All("f", Function(Real(), Real()),
            All("g", Function(Real(), Real()), All("c", Real(), equation)));
    }

    private static Formula ApproxErrorFormula()
    {
        var f = Id("f");
        var c = Id("c");
        var g = Id("g");
        var j = Id("J");
        var x = Id("x");
        var residual = Lambda("x", Ici(), Sub(Call("f", Call("val", x)), Call("g", Call("val", x))));
        var witness = And(Call("IsAdmissible", g),
            And(Call("BddAbove", Call("Set.range", residual)),
                And(Call("BddBelow", Call("Set.range", residual)),
                    Eq(j, Call("approxCost", f, g, c)))));
        var set = Seq(OpenBrace, j, Colon, Sp, Real(), Sp, Bar, Sp, Some("g", Function(Real(), Real()), witness), CloseBrace);
        var equation = Eq(Call("approxError", f, c), Call("sInf", set));
        return All("f", Function(Real(), Real()), All("c", Real(), equation));
    }

    private static Formula OperatorMonotoneFormula()
    {
        var n = Id("n");
        var a = Id("A");
        var b = Id("B");
        var f = Id("f");
        var matrix = Matrix(n);
        var body = Imp(Call("Matrix.PosSemidef", a),
            Imp(Call("Matrix.PosSemidef", b),
                Imp(Call("LE.le", a, b), Call("LE.le", Call("cfc", f, a), Call("cfc", f, b)))));
        var equation = Iff(Call("OperatorMonotoneOn", f), All("n", Nat(),
            All("A", matrix, All("B", matrix, body))));
        return All("f", Function(Real(), Real()), equation);
    }

    private static Formula ClaimFormula()
    {
        var f = Id("f");
        var x = Id("x");
        var c = Id("c");
        var body = Imp(All("x", Real(), Imp(Call("LE.le", D(0), x), Call("LE.le", D(0), Call("f", x)))),
            Imp(Call("OperatorMonotoneOn", f),
                All("c", Real(), Imp(Call("LT.lt", D(0), c),
                    Call("LE.le", Call("approxError", f, c), Call("f", c))))));
        return Iff(Id("claim"), All("f", Function(Real(), Real()), body));
    }

    private static Formula ResultFormula() => Seq(Neg, Sp, Id("claim"));
}
