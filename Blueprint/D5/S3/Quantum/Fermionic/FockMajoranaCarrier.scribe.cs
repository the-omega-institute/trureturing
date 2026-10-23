using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

#pragma warning disable IDE0051 // Shared DSL helper vocabulary intentionally exceeds each document formula set.
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class FockMajoranaCarrierDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/FockMajoranaCarrier.";
    private const string Note = "D5/L/QuantumBounds/negari2026gaussianapproximation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Occupation-space Majoranas satisfy Clifford relations and reverse number parity.",
        H("Majorana matrices on fermionic Fock space"), Blocks(
            Paragraph(Text("Natural subtraction is truncated at zero. All other divisions are in Real or Complex. Scalar casts retain their target type. Matrix products are operator products, and Matrix.conjTranspose is conjugate transpose. Subtype.val is the value of a density; Equiv.symm applied to CStarMatrix.ofMatrix recovers its ordinary matrix. Assignment N is the occupation basis Fin N → Bool. Implicit Lean mode and dimension arguments may be displayed explicitly. Bracketed Fintype, DecidableEq and Nonempty assumptions are anonymous instance arguments.")),
            Node("majorana", "The two Majoranas of a mode", MajoranaDefinition(),
                "From the creation and annihilation operators we define Hermitian Majorana operators by [page 4, equation (11)]: γ₂ⱼ₋₁ = cⱼ + cⱼ†, γ₂ⱼ = i(cⱼ − cⱼ†), j = 1, …, m. Here b=false denotes the first operator and b=true the second. The carrier uses N modes in the fixed increasing order.", DescribeRole.Definition),
            Node("numberParity", "Number parity as an operator power", ParityDefinition(),
                "“The number operator and parity operator are given by” [printed page 3]: N̂ = ∑ⱼ₌₁ᵐ cⱼ†cⱼ, P = (−1)^N̂. The operator-power convention is P = exp(iπN̂). Its diagonal form follows from the occupation-factor calculation of the number operator.", DescribeRole.Definition),
            Node("numberOperator", "Number operator", NumberOperatorDefinition(),
                "“The number operator and parity operator are given by” [printed page 3]: N̂ = ∑ⱼ₌₁ᵐ cⱼ†cⱼ, P = (−1)^N̂. Here fullC is the Jordan–Wigner annihilator and N counts all global modes.", DescribeRole.Definition),
            Node("numberOperator_eq_diagonal", "Number operator in the occupation basis", NumberOperatorDiagonal(),
                "The explicit occupation-factor calculation identifies the operator sum with the diagonal matrix of the occupied-mode count.", DescribeRole.Theorem),
            Node("numberParity_eq_diagonal", "Number parity in the occupation basis", ParityDiagonal(),
                "The diagonal exponential evaluates to exp(iπ times the integer occupation count), hence to (−1) raised to that count.", DescribeRole.Theorem),
            Node("majorana_clifford_and_parity", "Clifford relations and odd parity", Properties(),
                "They satisfy the Clifford relations [page 4, equation (12)]: {γₚ,γ_q} = 2δₚ,q 1, γₚ† = γₚ. The displayed statement verifies these relations for the actual Jordan–Wigner matrices and also verifies that number parity is a Hermitian involution which anticommutes with each generator. Products of two generators consequently commute with number parity.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role) => Describe.Lean(
        DescribeId.Create("fgauss-fock-" + name.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
        AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
        Blocks(Paragraph(Text(prose))), role);

    private static Formula Id(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] xs) => name switch
    {

        "ProdType" or "PairType" => Qualified("Prod", xs),
        "SumType" => Qualified("Sum", xs),
        "pair" => Qualified("Prod.mk", xs),
        "fst" => Qualified("Prod.fst", xs),
        "snd" => Qualified("Prod.snd", xs),
        "asReal" => Cast(xs[0], "Real"),
        "asComplex" => Cast(xs[0], "Complex"),
        "asInt" => Cast(xs[0], "Int"),
        "card" => Qualified("Fintype.card", xs),
        "edgeCount" or "edgeCard" => Qualified("Finset.card", Qualified("SimpleGraph.edgeFinset", xs)),
        "edgeSet" => Qualified("SimpleGraph.edgeSet", xs),
        "IsRegularOfDegree" => Qualified("SimpleGraph.IsRegularOfDegree", xs),
        "out" => Qualified("Sym2.out", Qualified("Subtype.val", xs)),
        "densityValue" => Qualified("Subtype.val", xs),
        "densityMatrix" => new Formula.Apply(Qualified("Equiv.symm", Qualified("CStarMatrix.ofMatrix")), [Qualified("Subtype.val", xs)]),
        "matrixOf" => new Formula.Apply(Qualified("Equiv.symm", Qualified("CStarMatrix.ofMatrix")), [.. xs]),
        "ofMatrix" => Qualified("CStarMatrix.ofMatrix", xs),
        "IsHermitian" => Qualified("Matrix.IsHermitian", xs),
        "transpose" => Qualified("Matrix.transpose", xs),
        "diagonal" => Qualified("Matrix.diagonal", xs),
        "trace" => Qualified("Matrix.trace", xs),
        "matrixSingle" => Qualified("Matrix.single", xs),
        "sqrt" or "squareRoot" => Qualified("Real.sqrt", xs),
        "log" => Qualified("Real.log", xs),
        "exp" => Qualified("NormedSpace.exp", xs),
        "pi" => Qualified("Real.pi"),
        "ComplexI" => Qualified("Complex.I"),
        "smul" => Qualified("SMul.smul", xs),
        "inv" => Qualified("Inv.inv", xs),
        "neg" => new Formula.Negate(xs[0]),
        "Fun" => new Formula.TypeArrow(xs[0], xs[1]),
        "M" => Qualified("Matrix", xs[0], xs[0], new Formula.Symbol(FormulaIdentifier.Create("Complex"))),
        "realIdentity" => Parenthesized(Seq(D(1), Colon, Qualified("Matrix", xs[0], xs[0], new Formula.Symbol(FormulaIdentifier.Create("Real"))))),
        "zero" => Parenthesized(Seq(D(0), Colon, xs[0])),
        "inl" => Qualified("Sum.inl", xs),
        "inr" => Qualified("Sum.inr", xs),
        "fromBlocks" => Qualified("Matrix.fromBlocks", xs),
        "Matrix2x2" => Seq(Bang, Bang, OpenBracket, xs[0], Comma, xs[1], Semi, xs[2], Comma, xs[3], CloseBracket),
        "letInstance" => Seq(FormulaDsl.Id("letI"), Sp, Colon, FormulaDsl.Eq, Sp, xs[0], Semi, Sp, xs[1]),
        "coordinateCouplingFamily" => Qualified("coordinateCoupling", xs),
        "coordinateComap" => Qualified("SimpleGraph.comap", Qualified("coordinateGraph", xs[0], Qualified("Index", xs[1])), xs[2]),
        "equivInverse" => new Formula.Apply(Qualified("Equiv.symm", xs[0]), [xs[1]]),
        "inverseEquiv" => Qualified("Equiv.symm", xs),
        _ => new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. xs])
    };
    private static Formula Qualified(string name, params Formula[] arguments)
    {
        var parts = name.Split('.');
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count != 0) items.Add(Dot);
            items.Add(Operatorname);
            items.Add(Grp(FormulaDsl.Id(part)));
        }
        Formula function = Seq(items.ToArray());
        return arguments.Length == 0 ? function : new Formula.Apply(function, [.. arguments]);
    }
    private static Formula Cast(Formula value, string type) =>
        Parenthesized(Seq(value, Colon, new Formula.Symbol(FormulaIdentifier.Create(type))));
    private static Formula LambdaTerm(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Parenthesized(Seq(new Formula.Symbol(FormulaIdentifier.Create(name)), Colon, type)), Mapsto, Parenthesized(body));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula lhs, Formula rhs) =>
        new Formula.Relation(lhs, FormulaRelationOperator.Equal, rhs);
    private static Formula Add(Formula lhs, Formula rhs) =>
        new Formula.Binary(lhs, FormulaBinaryOperator.Add, rhs);
    private static Formula Sub(Formula lhs, Formula rhs) =>
        new Formula.Binary(lhs, FormulaBinaryOperator.Subtract, rhs);
    private static Formula Mul(Formula lhs, Formula rhs) =>
        new Formula.Binary(lhs, FormulaBinaryOperator.Multiply, rhs);
    private static Formula Smul(Formula scalar, Formula value) =>
        Call("smul", scalar, value);
    private static Formula And(Formula lhs, Formula rhs) =>
        new Formula.Logic(Parenthesized(lhs), FormulaLogicOperator.And, Parenthesized(rhs));
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(Id(name), Colon, type, Sp, Mapsto, Sp, body);
    private static Formula M(Formula n, Formula p) =>
        Call("majorana", n, Call("fst", p), Call("snd", p));
    private static Formula P(Formula n) => Call("numberParity", n);
    private static Formula One(Formula n) => Parenthesized(Seq(D(1), Colon, Call("FullOperator", n)));
    private static Formula ComplexValue(Formula x) => Call("asComplex", x);

    private static Formula NumberOperatorDefinition()
    {
        var n = Id("N"); var j = Id("j");
        var c = Call("fullC", n, j);
        return All("N", Id("Nat"), Eq(Call("numberOperator", n),
            SumAt("j", Call("Fin", n), Mul(new Formula.Power(c, Star), c))));
    }

    private static Formula NumberOperatorDiagonal()
    {
        var n = Id("N"); var s = Id("s");
        return All("N", Id("Nat"), Eq(Call("numberOperator", n),
            Call("diagonal", Lambda("s", Call("Assignment", n),
                ComplexValue(Call("occupationCount", s))))));
    }

    private static Formula ParityDefinition()
    {
        var n = Id("N");
        return All("N", Id("Nat"), Eq(P(n),
            Call("exp", Smul(Mul(Call("pi"), Call("ComplexI")),
                Call("numberOperator", n)))));
    }

    private static Formula SumAt(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(Id(name), Colon, type)), Parenthesized(body));

    private static Formula MajoranaDefinition()
    {
        var n = Id("N"); var j = Id("j"); var b = Id("b");
        var c = Call("fullC", n, j);
        var adjoint = new Formula.Power(c, Star);
        return All("N", Id("Nat"), All("j", Call("Fin", n), All("b", Id("Bool"),
            Eq(Call("majorana", n, j, b), Call("ite", b,
                Call("smul", Call("ComplexI"), Parenthesized(Sub(c, adjoint))), Add(c, adjoint))))));
    }

    private static Formula ParityDiagonal()
    {
        var n = Id("N"); var s = Id("s");
        var entry = new Formula.Power(Parenthesized(Seq(Minus, ComplexValue(D(1)))), Call("occupationCount", s));
        return All("N", Id("Nat"), Eq(P(n), Call("diagonal",
            Lambda("s", Call("Assignment", n), entry))));
    }

    private static Formula Properties()
    {
        var n = Id("N"); var p = Id("p"); var q = Id("q");
        var labels = Call("PairType", Call("Fin", n), Id("Bool"));
        var mp = M(n,p); var mq = M(n,q);
        var car = All("p", labels, All("q", labels,
            Eq(Add(Mul(mp,mq), Mul(mq,mp)), Call("ite", Eq(p,q),
                Call("smul", ComplexValue(D(2)), One(n)), Call("zero", Call("FullOperator", n))))));
        var odd = All("p", labels, Eq(Add(Mul(P(n),mp), Mul(mp,P(n))),
            Call("zero", Call("FullOperator", n))));
        return All("N", Id("Nat"), And(Call("IsHermitian", P(n)),
            And(Eq(Mul(P(n),P(n)), One(n)),
                And(All("p", labels, Call("IsHermitian", M(n,p))), And(car,odd)))));
    }
}
