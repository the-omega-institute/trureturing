using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class InteriorPolynomialRealCalculusDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/InteriorPolynomialRealCalculus";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordinary real calculus for independent trial polynomials", H("Ordinary real calculus for independent trial polynomials"), Blocks(
            Describe.Lean(DescribeId.Create("interiorpolynomialrealcalculus-hasfderivat-slice"),
                DeclarationHandle.Create(Module + ".hasFDerivAt_slice"), H("Ordinary real polynomial slice derivative"),
                StatementSource.FromAuthor(Disp(SliceFormula())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For an arbitrary real polynomial F in two independent trial coordinates and any target coordinate type, hold every target coordinate constant. Formal pderiv in trial x and y gives the ordinary real Frechet derivative: eval(pderiv_x F) times reCLM plus eval(pderiv_y F) times imCLM. Polynomial induction proves the constant, sum and multiplication cases using the existing pderiv rules and real calculus."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("interiorpolynomialrealcalculus-real-det"),
                DeclarationHandle.Create(Module + ".real_det"), H("The real two by two determinant"),
                StatementSource.FromAuthor(Disp(DeterminantFormula())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The columns of the ordinary real derivative are its values on 1 and I; the rows are real and imaginary outputs. The basisOneI change-of-basis theorem identifies this two by two determinant with LinearMap.det over the real field."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("interiorpolynomialrealcalculus-cleared-jacobian"),
                DeclarationHandle.Create(Module + ".cleared_jacobian"), H("Clearing scales the two derivative rows"),
                StatementSource.FromAuthor(Disp(JacobianFormula())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Let the polynomial rows agree locally with c times Re(f) and e times Im(f). At a common root of f, differentiable clearing factors contribute no derivative-of-factor term. Uniqueness of the ordinary real derivative identifies the formal trial Jacobian with c(z) e(z) det_R(D). All target coordinates remain fixed. No holomorphic derivative is used."))), DescribeRole.Theorem),
            Paragraph(Text("These are parameter-locus statements for finite native unnormalized MPS observations. Canonical chart dominance, genericity on actual full-state or actual raw-density images, and the full Critch-Morton C9 problem remain separate obligations. No solved-open-problem credit, clock, dynamics, energy, positive physical inverse or thermodynamic cost follows.")))));

    private static Formula C => Id("Complex");
    private static Formula R => Id("Real");
    private static Formula SliceFormula()
    {
        var f=Id("F"); var t=Id("theta"); var z=Id("z");
        return Bind([("K",Id("Type")),("F",Call("RealTrialPolynomial",Id("K"))),("theta",Call("Function",Id("K"),R)),("z",C)],
            Call("HasFDerivAt",LambdaOf("w",C,Call("eval",Call("slice",t,Id("w")),f)),Call("sliceDerivative",f,t,z),z));
    }
    private static Formula DeterminantFormula() => All("D",Call("RealContinuousLinearEnd",C),
        Eq(Call("det",Call("toLinearMap",Id("D"))),Sub(Mul(Call("re",Call("D",D(1))),Call("im",Call("D",Id("I")))),Mul(Call("re",Call("D",Id("I"))),Call("im",Call("D",D(1)))))));
    private static Formula JacobianFormula()
    {
        var z=Id("z"); var w=Id("w"); var t=Id("theta"); var f=Id("f"); var d=Id("D"); var c=Id("c"); var e=Id("e");
        return Bind([("K",Id("Type")),("F",Call("RealTrialPolynomial",Id("K"))),("H",Call("RealTrialPolynomial",Id("K"))),
            ("theta",Call("Function",Id("K"),R)),("z",C),("f",Call("Function",C,C)),("D",Call("RealContinuousLinearEnd",C)),
            ("c",Call("Function",C,R)),("e",Call("Function",C,R))],
            Imp(And(Eq(Call("f",z),D(0)),Call("HasFDerivAt",f,d,z),Call("DifferentiableAt",R,c,z),Call("DifferentiableAt",R,e,z),
                Call("EventuallyEq",Call("nhds",z),LambdaOf("w",C,Call("eval",Call("slice",t,w),Id("F"))),LambdaOf("w",C,Mul(Call("c",w),Call("re",Call("f",w))))),
                Call("EventuallyEq",Call("nhds",z),LambdaOf("w",C,Call("eval",Call("slice",t,w),Id("H"))),LambdaOf("w",C,Mul(Call("e",w),Call("im",Call("f",w)))))),
                Eq(Call("eval",Call("slice",t,z),Call("trialJacobian",Id("F"),Id("H"))),Mul(Mul(Call("c",z),Call("e",z)),Call("det",Call("toLinearMap",d))))));
    }

    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Id(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Bind((string Name, Formula Type)[] xs, Formula b) { for (var i = xs.Length - 1; i >= 0; --i) b = All(xs[i].Name, xs[i].Type, b); return b; }
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula LambdaOf(string name, Formula type, Formula body) => Par(Seq(LambdaLower, Sp, Par(Seq(Id(name), Colon, Sp, type)), Sp, Mapsto, Sp, Par(body)));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula And(params Formula[] xs) => xs.Aggregate((a, b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b)));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
}
