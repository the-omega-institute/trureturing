using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

#pragma warning disable IDE0051 // Shared DSL helper vocabulary intentionally exceeds each document formula set.
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class JointSignProjectorsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent sign reversals give a joint minus projector with exact trace.",
        H("The joint minus sector of commuting involutions"), Blocks(
            Paragraph(Text("Natural subtraction is truncated at zero. All other divisions are in Real or Complex. Scalar casts retain their target type. Matrix products are operator products, and Matrix.conjTranspose is conjugate transpose. Subtype.val is the value of a density; Equiv.symm applied to CStarMatrix.ofMatrix recovers its ordinary matrix. Assignment N is the occupation basis Fin N → Bool. Implicit Lean mode and dimension arguments may be displayed explicitly. Bracketed Fintype, DecidableEq and Nonempty assumptions are anonymous instance arguments.")),
            Describe.Lean(DescribeId.Create("fgauss-joint-sign-projection"),
                DeclarationHandle.Create("D5/S3/Quantum/Fermionic/JointSignProjectors.joint_sign_projection"),
                H("Exact trace and simultaneous minus eigenvalues"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The B operators are commuting Hermitian involutions. For each i, the involution U(i) reverses B(i) and commutes with every other B(j). The joint minus projection has trace card(Omega)/2^card(I). In particular it is nonzero when Omega is nonempty. It commutes with every matrix which commutes with all the B operators. The construction multiplies the commuting projections (1−B(i))/2. Induction inserts one factor at a time; conjugation by its sign reversal cancels the mixed trace, so each inserted factor halves the trace."))), DescribeRole.Theorem))));

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
    private static Formula ExistsIn(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula lhs, Formula rhs) =>
        new Formula.Relation(lhs, FormulaRelationOperator.Equal, rhs);
    private static Formula Ne(Formula lhs, Formula rhs) =>
        new Formula.Relation(lhs, FormulaRelationOperator.NotEqual, rhs);
    private static Formula Mul(Formula lhs, Formula rhs) =>
        new Formula.Binary(lhs, FormulaBinaryOperator.Multiply, rhs);
    private static Formula And(Formula lhs, Formula rhs) =>
        new Formula.Logic(Parenthesized(lhs), FormulaLogicOperator.And, Parenthesized(rhs));
    private static Formula Implies(Formula lhs, Formula rhs) =>
        new Formula.Logic(Parenthesized(lhs), FormulaLogicOperator.Implies, Parenthesized(rhs));
    private static Formula At(string name, Formula index) => Call("val", Id(name), index);

    private static Formula Statement()
    {
        var labels = Id("I"); var omega = Id("Omega");
        var i = Id("i"); var j = Id("j"); var p = Id("P"); var q = Id("Q");
        var matrix = Call("M", omega);
        var one = Parenthesized(Seq(D(1), Colon, matrix));
        var bi = At("B",i); var bj = At("B",j); var ui = At("U",i);
        var hB = All("i", labels, And(Call("IsHermitian",bi),Eq(Mul(bi,bi),one)));
        var hBB = All("i", labels, All("j", labels, Call("Commute",bi,bj)));
        var hU = All("i", labels, Eq(Mul(ui,ui),one));
        var hflip = All("i", labels, Eq(Mul(ui,bi),Call("neg",Mul(bi,ui))));
        var hfix = All("i", labels, All("j", labels, Implies(Ne(i,j),Call("Commute",ui,bj))));
        var hypotheses = And(hB,And(hBB,And(hU,And(hflip,hfix))));
        var conclusion = ExistsIn("P",matrix,And(Call("IsStarProjection",p),
            And(Eq(Call("trace",p),new Formula.Fraction(Call("asComplex",Call("card",omega)),
                new Formula.Power(Call("asComplex",D(2)),Call("card",labels)))),
                And(All("i",labels,Eq(Mul(bi,p),Call("neg",p))),
                    All("Q",matrix,Implies(All("i",labels,Call("Commute",q,bi)),
                        Call("Commute",q,p)))))));
        return All("I",Id("Type"),All("Omega",Id("Type"),Seq(
            OpenBracket,Call("Fintype",labels),CloseBracket,Sp,
            OpenBracket,Call("Fintype",omega),CloseBracket,Sp,
            OpenBracket,Call("DecidableEq",omega),CloseBracket,Sp,
            All("B",Call("Fun",labels,matrix),All("U",Call("Fun",labels,matrix),
                Implies(hypotheses,conclusion))))));
    }
}
