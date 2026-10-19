using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class SingleEntrySpectralGapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/SingleEntrySpectralGap.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The single-entry secular root in free-mode coordinates.",
        H("Rank-one spectral extension"),
        Blocks(
            BasisNode("localBasis", "Local product basis", "Rows are the empty and occupied configurations and columns are the zero and nonzero free modes. The local basis is [[1,1],[a/b,-1]]."),
            BasisNode("localInverse", "Local inverse basis", "In the same coordinate order, the local inverse is [[b/(a+b),b/(a+b)],[a/(a+b),-b/(a+b)]]."),
            BasisNode("productBasis", "Configuration reconstruction", "The finite product basis P has entry P(sigma,S) equal to the product over sites of the corresponding local basis entry, using membership in sigma and S as Boolean row and column indices."),
            BasisNode("productInverse", "Free-mode extraction", "The finite product inverse T has entry T(S,sigma) equal to the product over sites of the local inverse entry, using membership in S and sigma as Boolean indices."),
            BasisNode("coordinateTransform", "Full mode extraction", "The full matrix extends the product inverse by an identity at the repressed coordinate and zero cross blocks."),
            BasisNode("inverseTransform", "Full configuration reconstruction", "The full inverse extends the product basis by an identity at the repressed coordinate and zero cross blocks."),
            Describe.Lean(DescribeId.Create("single-entry-mode-negative-generator"),
                DeclarationHandle.Create(Prefix + "modeNegativeGenerator"), H("Mode matrix"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The index set is Option(Finset(I)), with none the attached repressed coordinate. Writing H for the sum of all subset coordinates, the matrix B acts by (Bx)(none)=h x(none)-e H and (Bx)(S)=s(S)x(S)+W(S)(e H-h x(none)). Here e=eta and h=theta. These are free-mode coordinates; the matrix is not defined by assuming its eigenvalues or its secular equation. A product change of basis is required to identify B with the actual configuration generator."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("single-entry-secular-least-mode-eigenvalue"),
                DeclarationHandle.Create(Prefix + "secular_root_least_mode_eigenvalue"), H("Least positive mode eigenvalue"),
                StatementSource.FromAuthor(Formula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every nonempty finite site family and positive rates, there is a positive scalar l below every site rate, satisfying F(l)=0, with a nonzero vector x satisfying Bx=l x. Every positive real m admitting such a nonzero eigenvector satisfies l<=m. The proof first eliminates the subset coordinates: x(S)=l W(S)x(none)/(s(S)-l). If x(none)=0, every coordinate is zero, contradicting the eigenvector premise. Summing the solved coordinates gives F(l)=0. Conversely F(l)=0 produces an eigenvector by x(none)=1 and the displayed subset formula. The earlier unique-root theorem then excludes every smaller positive eigenvalue. This theorem concerns the mode matrix and does not assert a slow-tail coefficient."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("single-entry-secular-least-generator-eigenvalue"),
                DeclarationHandle.Create(Prefix + "secular_root_least_generator_eigenvalue"), H("Least positive eigenvalue of the actual generator"),
                StatementSource.FromAuthor(FullFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The rates k are the independently specified actual binding and unbinding rates at each finite site, together with the two positive attachment rates. The configuration generator Q is the sum of its actual directed transition edges, on Option(Finset(I)), and the theorem concerns -Q. An explicit product change of basis has local matrix [[1,1],[a/b,-1]] and local inverse [[b/(a+b),b/(a+b)],[a/(a+b),-b/(a+b)]]. Multiplying these local matrices across sites gives two inverse finite matrices. The actual local-jump backward equation shows that the inverse product transform intertwines Q with -B. Thus nonzero eigenvectors transport in both directions, and the mode-matrix theorem gives the full generator's least positive real eigenvalue. The upper bound l<s(i) holds at every site. This spectral conclusion does not identify a return spectral coefficient or establish the requested association-tail limit."))), DescribeRole.Theorem),
            Helper("transform_inverse", "The product transforms are inverse", InverseFormula(), "For every finite site family with a(i),b(i)>0, inverseTransform(a,b) times coordinateTransform(a,b) is the identity matrix. The proof expands the subset sum as a product of local two-by-two matrix products."),
            Helper("inverse_empty", "The injection has the specified weights", EmptyFormula(), "For every finite site family with positive a and b, productInverse(a,b,S,empty) equals the independently defined modeWeight(a,b,S), at every subset S."),
            Helper("transform_generator", "Intertwining the actual generator", IntertwiningFormula(), "For every positive rate record k and every real vector p on actual configurations, T(Qp)=-B(Tp). This uses the independently specified local jumps through the backward-generator duality and the computed action of each local product mode."),
            Helper("action_none", "The repressed row of the extended matrix", NoneActionFormula(), "For every finite family of real rates and every real vector x, (Bx)(none)=h x(none)-e sum(T,x(some T)). This row identity is used by Schur elimination and the stationary equations."),
            Helper("action_some", "A mode row of the extended matrix", ActionFormula(), "For every finite family of real a,b, real attachment parameters e,h, vector x and subset S, (Bx)(some S)=s(S)x(some S)+W(S)(e sum(T,x(some T))-h x(none)). This algebraic action formula requires no positivity premise."),
            Helper("transform_empty", "Reading the empty configuration", TransformEmptyFormula(), "For positive binding and unbinding rates and every vector p, the actual empty-configuration coordinate p(some empty) equals the sum of all extracted subset-mode coordinates (Tp)(some S)."),
            Helper("sum_subset_product", "Subset expansion of a product", SumProductFormula(), "For every finite type and arbitrary real functions f,g, the sum over all subsets S of the product of f(i) on S and g(i) off S equals the product of f(i)+g(i). The identity is Mathlib's product-add theorem in the membership-indicator form used by the transforms."))));

    private static DocumentBlock BasisNode(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("single-entry-basis-" + name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static DocumentBlock Helper(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("single-entry-basis-" + name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new System.Collections.Generic.List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq(items.ToArray());
    }
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string v, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), domain, body);
    private static Formula Ex(string v, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(v), domain, body);
    private static Formula R() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Positive(Formula v) => Rel(D(0), FormulaRelationOperator.LessThan, v);
    private static Formula Matrix() => Call("modeNegativeGenerator", F.Id("a"), F.Id("b"), F.Id("e"), F.Id("h"));
    private static Formula Vector() => Seq(Call("Option", Call("Finset", F.Id("I"))), Sp, To, Sp, R());
    private static Formula EigenFor(string v, Formula l, Formula matrix) => Ex(v, Vector(), And(
        Rel(F.Id(v), FormulaRelationOperator.NotEqual, D(0)),
        Rel(Call("mulVec", matrix, F.Id(v)), FormulaRelationOperator.Equal, Call("smul", l, F.Id(v)))));
    private static Formula Eigen(string v, Formula l) => EigenFor(v, l, Matrix());
    private static Formula Formula()
    {
        var l = F.Id("l"); var m = F.Id("m"); var i = F.Id("i");
        var result = Ex("l", R(), And(Positive(l), And(
            All("i", F.Id("I"), Rel(l, FormulaRelationOperator.LessThan, Call("siteRate", F.Id("a"), F.Id("b"), i))), And(
            Rel(Call("secular", F.Id("a"), F.Id("b"), F.Id("e"), F.Id("h"), l), FormulaRelationOperator.Equal, D(0)), And(
            Eigen("x", l), All("m", R(), Imp(Positive(m), Imp(Eigen("y", m), Rel(l, FormulaRelationOperator.LessThanOrEqual, m)))))))));
        var rates = And(All("i", F.Id("I"), Positive(Call("a", i))), And(
            All("i", F.Id("I"), Positive(Call("b", i))), And(Positive(F.Id("e")), Positive(F.Id("h")))));
        var fn = Seq(F.Id("I"), Sp, To, Sp, R());
        var body = All("a", fn, All("b", fn, All("e", R(), All("h", R(), Imp(rates, result)))));
        return Disp(All("I", F.Id("Type"), Seq(
            OpenBracket, Call("Fintype", F.Id("I")), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", F.Id("I")), CloseBracket, Sp,
            OpenBracket, Call("Nonempty", F.Id("I")), CloseBracket, Sp, body)));
    }
    private static Formula FullFormula()
    {
        var l = F.Id("l"); var m = F.Id("m"); var i = F.Id("i"); var k = F.Id("k");
        var matrix = Call("neg", Call("generator", k));
        var root = Ex("l", R(), And(Positive(l), And(
            All("i", F.Id("I"), Rel(l, FormulaRelationOperator.LessThan, Call("siteRate", Call("a", k), Call("b", k), i))), And(
            Rel(Call("secular", Call("a", k), Call("b", k), Call("eta", k), Call("theta", k), l), FormulaRelationOperator.Equal, D(0)), And(
            EigenFor("x", l, matrix), All("m", R(), Imp(Positive(m), Imp(EigenFor("y", m, matrix), Rel(l, FormulaRelationOperator.LessThanOrEqual, m)))))))));
        return Disp(All("I", F.Id("Type"), Seq(
            OpenBracket, Call("Fintype", F.Id("I")), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", F.Id("I")), CloseBracket, Sp,
            OpenBracket, Call("Nonempty", F.Id("I")), CloseBracket, Sp,
            All("k", Call("Rates", F.Id("I")), root))));
    }
    private static Formula FiniteBody(Formula body) => All("I", F.Id("Type"), Seq(
        OpenBracket, Call("Fintype", F.Id("I")), CloseBracket, Sp,
        OpenBracket, Call("DecidableEq", F.Id("I")), CloseBracket, Sp, body));
    private static Formula PositiveFunctions(Formula body)
    {
        var fn = Seq(F.Id("I"), Sp, To, Sp, R());
        var premise = And(All("i", F.Id("I"), Positive(Call("a", F.Id("i")))), All("i", F.Id("I"), Positive(Call("b", F.Id("i")))));
        return FiniteBody(All("a", fn, All("b", fn, Imp(premise, body))));
    }
    private static Formula InverseFormula() => Disp(PositiveFunctions(Rel(
        Call("matrixMul", Call("inverseTransform", F.Id("a"), F.Id("b")), Call("coordinateTransform", F.Id("a"), F.Id("b"))), FormulaRelationOperator.Equal, D(1))));
    private static Formula EmptyFormula() => Disp(PositiveFunctions(All("S", Call("Finset", F.Id("I")), Rel(
        Call("productInverse", F.Id("a"), F.Id("b"), F.Id("S"), Emptyset), FormulaRelationOperator.Equal,
        Call("modeWeight", F.Id("a"), F.Id("b"), F.Id("S"))))));
    private static Formula IntertwiningFormula()
    {
        var k = F.Id("k"); var p = F.Id("p");
        var t = Call("coordinateTransform", Call("a", k), Call("b", k));
        var b = Call("modeNegativeGenerator", Call("a", k), Call("b", k), Call("eta", k), Call("theta", k));
        return Disp(FiniteBody(All("k", Call("Rates", F.Id("I")), All("p", Vector(), Rel(
            Call("mulVec", t, Call("mulVec", Call("generator", k), p)), FormulaRelationOperator.Equal,
            Call("neg", Call("mulVec", b, Call("mulVec", t, p))))))));
    }
    private static Formula CubeSum(Formula vector) => Seq(new Formula.Subscript(Sum, Seq(F.Id("T"), Colon, Call("Finset", F.Id("I")))), Sp, Call("apply", vector, Call("some", F.Id("T"))));
    private static Formula TransformEmptyFormula() => Disp(PositiveFunctions(All("p", Vector(), Rel(
        Call("apply", F.Id("p"), Call("some", Emptyset)), FormulaRelationOperator.Equal,
        CubeSum(Call("mulVec", Call("coordinateTransform", F.Id("a"), F.Id("b")), F.Id("p")))))));
    private static Formula NoneActionFormula()
    {
        var x = F.Id("x");
        var fn = Seq(F.Id("I"), Sp, To, Sp, R());
        var rhs = Seq(F.Id("h"), Sp, Cdot, Sp, Call("apply", x, Call("none")), Sp, Minus, Sp,
            F.Id("e"), Sp, Cdot, Sp, CubeSum(x));
        return Disp(FiniteBody(All("a", fn, All("b", fn, All("e", R(), All("h", R(), All("x", Vector(), Rel(
            Call("apply", Call("mulVec", Matrix(), x), Call("none")), FormulaRelationOperator.Equal, rhs))))))));
    }
    private static Formula ActionFormula()
    {
        var x = F.Id("x"); var s = F.Id("S");
        var fn = Seq(F.Id("I"), Sp, To, Sp, R());
        var rhs = Seq(Call("subsetRate", F.Id("a"), F.Id("b"), s), Sp, Cdot, Sp, Call("apply", x, Call("some", s)), Sp, Plus, Sp,
            Call("modeWeight", F.Id("a"), F.Id("b"), s), Sp, Cdot, Sp, Open,
            F.Id("e"), Sp, Cdot, Sp, CubeSum(x), Sp, Minus, Sp,
            F.Id("h"), Sp, Cdot, Sp, Call("apply", x, Call("none")), Close);
        return Disp(FiniteBody(All("a", fn, All("b", fn, All("e", R(), All("h", R(), All("x", Vector(), All("S", Call("Finset", F.Id("I")), Rel(
            Call("apply", Call("mulVec", Matrix(), x), Call("some", s)), FormulaRelationOperator.Equal, rhs)))))))));
    }
    private static Formula SumProductFormula()
    {
        var f = F.Id("f"); var g = F.Id("g"); var i = F.Id("i"); var s = F.Id("S");
        var fn = Seq(F.Id("I"), Sp, To, Sp, R());
        var lhs = Seq(new Formula.Subscript(Sum, Seq(s, Colon, Call("Finset", F.Id("I")))), Sp,
            new Formula.Subscript(Prod, Seq(i, Colon, F.Id("I"))), Sp,
            Call("ite", Call("mem", i, s), Call("apply", f, i), Call("apply", g, i)));
        var rhs = Seq(new Formula.Subscript(Prod, Seq(i, Colon, F.Id("I"))), Sp, Open, Call("apply", f, i), Sp, Plus, Sp, Call("apply", g, i), Close);
        return Disp(FiniteBody(All("f", fn, All("g", fn, Rel(lhs, FormulaRelationOperator.Equal, rhs)))));
    }
}
