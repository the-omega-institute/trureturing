using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

#pragma warning disable IDE0051 // Shared DSL helper vocabulary intentionally exceeds each document formula set.
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class ConferenceMatricesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/ConferenceMatrices.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Recursive skew conference matrices have order a power of two and flat square.",
        H("Recursive skew conference matrices"),
        Blocks(
            Paragraph(Text("Natural subtraction is truncated at zero. All other divisions are in Real or Complex. Scalar casts retain their target type. Matrix products are operator products, and Matrix.conjTranspose is conjugate transpose. Subtype.val is the value of a density; Equiv.symm applied to CStarMatrix.ofMatrix recovers its ordinary matrix. Assignment N is the occupation basis Fin N → Bool. Implicit Lean mode and dimension arguments may be displayed explicitly. Bracketed Fintype, DecidableEq and Nonempty assumptions are anonymous instance arguments.")),
            Node("Index", "Recursive labels", new Formula.Aligned([
                Eq(Call("Index", D(0)), Call("Fin", D(2))),
                All("r", N("Nat"), Eq(Call("Index", Add(N("r"), D(1))),
                    Call("SumType", Index(N("r")), Index(N("r")))))]),
                "The displayed equations define the recursive label type.", DescribeRole.Definition),
            Node("indexFintype", "Finite enumeration", new Formula.Aligned([
                Eq(Call("indexFintype", D(0)), Call("inferInstanceAs", Call("Fintype", Call("Fin", D(2))))),
                All("r", N("Nat"), Eq(Call("indexFintype", Add(N("r"), D(1))),
                    Call("letInstance", Call("indexFintype", N("r")),
                        Call("inferInstanceAs", Call("Fintype", Call("SumType", Index(N("r")), Index(N("r"))))))))]),
                "At order zero the enumeration is the finite-two enumeration. Each subsequent enumeration is the finite disjoint-sum enumeration using the preceding enumeration as a local instance.", DescribeRole.Definition),
            Node("indexDecidableEq", "Decidable equality", new Formula.Aligned([
                Eq(Call("indexDecidableEq", D(0)), Call("inferInstanceAs", Call("DecidableEq", Call("Fin", D(2))))),
                All("r", N("Nat"), Eq(Call("indexDecidableEq", Add(N("r"), D(1))),
                    Call("letInstance", Call("indexDecidableEq", N("r")),
                        Call("inferInstanceAs", Call("DecidableEq", Call("SumType", Index(N("r")), Index(N("r"))))))))]),
                "At order zero equality is finite-two equality. At every subsequent order equality is disjoint-sum equality using the preceding equality instance.", DescribeRole.Definition),
            Node("conference", "Matrix recursion", new Formula.Aligned([
                Eq(C(D(0)), Call("Matrix2x2", D(0), D(1), Negate(D(1)), D(0))),
                All("r", N("Nat"), Eq(C(Add(N("r"), D(1))), Call("fromBlocks",
                    C(N("r")), Add(C(N("r")), One(N("r"))),
                    Sub(C(N("r")), One(N("r"))), Negate(C(N("r"))))))]),
                "The four blocks at each doubling are C, C+I, C-I and -C, in that order. All entries are integers.", DescribeRole.Definition),
            Node("conference_properties", "Order, skewness, signs and square", Properties(),
                "The recursive family has order 2^(r+1), zero diagonal and signed off-diagonal entries. Its square is minus the order minus one times the identity. Induction on the doubling step preserves the four-block multiplication identity as well as the signed-entry conditions.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role) => Describe.Lean(
        DescribeId.Create("fgauss-conference-" + name.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula N(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
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
    private static Formula Negate(Formula value) => Seq(Minus, Parenthesized(value));
    private static Formula Index(Formula r) => Call("Index", r);
    private static Formula C(Formula r) => Call("conference", r);
    private static Formula One(Formula r) =>
        Parenthesized(Seq(D(1), Colon, Call("Matrix", Index(r), Index(r), N("Int"))));

    private static Formula Properties()
    {
        var r = N("r");
        var i = N("i");
        var j = N("j");
        var cardinality = Call("card", Index(r));
        var entry = Call("val", C(r), i, j);
        return All("r", N("Nat"), Seq(
            Parenthesized(Eq(cardinality, new Formula.Power(D(2), Parenthesized(Add(r, D(1)))))),
            Land, Parenthesized(Eq(Call("transpose", C(r)), Negate(C(r)))),
            Land, Parenthesized(All("i", Index(r), Eq(Call("val", C(r), i, i), D(0)))),
            Land, Parenthesized(All("i", Index(r), All("j", Index(r), new Formula.Logic(
                Parenthesized(new Formula.Relation(i, FormulaRelationOperator.NotEqual, j)),
                FormulaLogicOperator.Implies, Parenthesized(new Formula.Logic(
                    Parenthesized(Eq(entry, D(1))), FormulaLogicOperator.Or,
                    Parenthesized(Eq(entry, Negate(D(1)))))))))),
            Land, Parenthesized(Eq(new Formula.Binary(C(r), FormulaBinaryOperator.Multiply, C(r)),
                Call("smul", Negate(Sub(Call("asInt", cardinality), D(1))), One(r))))));
    }
}
