using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class MittagLefflerBarnesKernelDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Analytic/braams2026barnesmittagport");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal Barnes kernel is integrable on exterior vertical contours.", H("The Mittag-Leffler Barnes kernel"), Blocks(
            Describe.Lean(DescribeId.Create("mittaglefflerbarneskernel-kernel"),
                DeclarationHandle.Create("D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.kernel"),
                H("The literal Barnes kernel"), StatementSource.FromAuthor(Disp(KernelFormula())),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("ComplexGamma is complex Gamma, log is the principal complex logarithm, and all real scalars are embedded into Complex. The formula uses the entire reciprocal Gamma, including its zeros."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("mittaglefflerbarneskernel-margin"),
                DeclarationHandle.Create("D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.margin"),
                H("The angular margin"), StatementSource.FromAuthor(Disp(All("alpha", R, All("z", Cx, Equal(Call("margin", V("alpha"), V("z")), Sub(Mul(Seq(Pi, Sp), Sub(Num(1), Div(V("alpha"), Num(2)))), Abs(Call("arg", Negate(V("z")))))))))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The strict exterior sector is exactly the set where margin(alpha,z) is positive."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("mittaglefflerbarneskernel-exists-line-majorant"),
                DeclarationHandle.Create("D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.exists_line_majorant"),
                H("A majorant on a vertical line"), StatementSource.FromAuthor(Disp(MajorantFormula())),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("For alpha positive and a real line c with sin(pi*c) nonzero, the constants C and K are independent of the line coordinate y. Reflection converts the two Gamma factors into pi/sin(pi*s), leaving the reciprocal Gamma bound and the exact principal-logarithm exponential norm. No series representation is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("mittaglefflerbarneskernel-integrable-line"),
                DeclarationHandle.Create("D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel.integrable_line"),
                H("Integrability in the strict exterior sector"), StatementSource.FromAuthor(Disp(IntegrableFormula())),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The polynomial-exponential majorant is integrable when the angular margin is positive. The reflected expression is measurable because reciprocal Gamma is entire; division by sine is a measurable operation."))),
                DescribeRole.Theorem),
            ExtraEntry("left-line", "leftLine", "The left contour sequence", All("n",N,Equal(Call("leftLine",V("n")),Sub(Div(Num(1),Num(2)),V("n")))), "The line indexed by n has real part one half minus n.", DescribeRole.Definition),
            ExtraEntry("left-numerator", "leftNumerator", "The shifted Gamma numerator", NumeratorDefinition(), "The finite product contains precisely the factors s+j with j<n. Each zero lies strictly to the right of the n-th closed strip. The shifted Gamma and Gamma(1-s) have positive real arguments on that strip. Reciprocal Gamma is entire, including at its zeros.", DescribeRole.Definition),
            ExtraEntry("left-numerator-holomorphic", "differentiableOn_leftNumerator", "Holomorphy on the closed strip", NumeratorHolomorphic(), "The two ordinary Gamma factors avoid all their poles by their positive real parts. The finite factors divided out do not vanish on the strip. Differentiability of reciprocal Gamma supplies the remaining factor without any denominator nonvanishing hypothesis.", DescribeRole.Theorem),
            ExtraEntry("left-factorization", "kernel_eq_leftNumerator", "The actual single-pole factorization", Factorization(), "Gamma recurrence factors the actual kernel as leftNumerator divided by s+n throughout the closed strip away from s=-n. This supplies the factorization field of the actual Mellin-Barnes data.", DescribeRole.Theorem),
            ExtraEntry("left-residue", "leftNumerator_residue", "The literal source coefficient", Residue(), "At s=-n the shifted Gamma is one, Gamma(1-s) is n factorial, and the remaining finite product is (-1)^n times n factorial. Exp(n*log(-z))=(-z)^n for nonzero z. Only the factorial is cancelled; reciprocal-Gamma zeros remain in scope.", DescribeRole.Theorem),
            ExtraEntry("gamma-line-majorant", "norm_line_le_recip_gamma", "The growing Gamma denominator", GammaLineBound(), "When beta-alpha*c is at least one half, the squared reciprocal-Gamma estimate retains Gamma(beta-alpha*c) in the denominator. Reflection and the actual angular margin give this estimate without a bounded-strip replacement constant.", DescribeRole.Theorem),
            ExtraEntry("half-line-sine", "abs_sin_leftLine", "The half-integer sine factor", All("n",N,Equal(Abs(Call("sin",Mul(Seq(Pi,Sp),Call("leftLine",V("n"))))),Num(1))), "Moving the line left by one changes the sine sign, so its absolute value remains one. This is used by the integral estimate and the actual contour integrability proof.", DescribeRole.Theorem),
            ExtraEntry("left-integral-bound", "norm_integral_leftLine_le", "The moving-line integral bound", IntegralLineBound(), "The entire vertical integral is bounded by its retained real-Gamma radial factor times the fixed integral of exp(-margin*abs(y)). This bound is used in the literal coefficient summability argument.", DescribeRole.Theorem),
            ExtraEntry("horizontal-limits", "horizontal_tendsto_zero", "Both horizontal limits", HorizontalLimits(), "On each finite real strip, the reciprocal-Gamma strip estimate and the far-horizontal sine lower bound give one polynomial-exponential majorant independent of the real coordinate. The interval integral is bounded by the strip width times that majorant. The positive angular margin forces both limits to zero.", DescribeRole.Theorem))));


    private static DocumentBlock ExtraEntry(string id, string name, string title, Formula statement, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("mittaglefflerbarneskernel-"+id),
            DeclarationHandle.Create("D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel."+name),
            H(title),StatementSource.FromAuthor(Disp(statement)),AssessedProvenance.FromRepo(Source),Blocks(Paragraph(Text(prose))),role);
    private static Formula KAt(Formula s) => Call("kernel",V("alpha"),V("beta"),V("z"),s);
    private static Formula NAt(Formula s) => Call("leftNumerator",V("alpha"),V("beta"),V("z"),V("n"),s);
    private static Formula Line(Formula c) => Map("y",R,KAt(Add(c,Mul(V("y"),Imaginary))));
    private static Formula Imaginary => Seq(Operatorname,Grp(F.Id("ComplexI")));
    private static Formula Parameters(Formula f) => All("alpha",R,All("beta",R,All("z",Cx,f)));
    private static Formula Strip(Formula s) => Call("mem",Call("re",s),Call("Icc",Call("leftLine",Add(V("n"),Num(1))),Call("leftLine",V("n"))));
    private static Formula Nonzero(Formula z) => Seq(z,Neq,Sp,Num(0));
    private static Formula Limit(Formula f,string filter) => Call("Tendsto",f,V(filter),Call("nhds",Num(0)));
    private static Formula And(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula NumeratorDefinition()
    {
        Formula s=V("s"), g=Mul(Mul(Call("ComplexGamma",Sub(Num(1),s)),Div(Num(1),Call("ComplexGamma",Sub(V("beta"),Mul(V("alpha"),s))))),Call("exp",Mul(Negate(s),Call("log",Negate(V("z"))))));
        Formula product=Call("product",Call("range",V("n")),Map("j",N,Add(s,V("j"))));
        Formula rhs=Div(Mul(g,Call("ComplexGamma",Add(Add(s,V("n")),Num(1)))),product);
        return Parameters(All("n",N,All("s",Cx,Equal(NAt(s),rhs))));
    }
    private static Formula NumeratorHolomorphic() => Parameters(All("n",N,
        Call("DifferentiableOn",Cx,Map("s",Cx,NAt(V("s"))),Call("preimage",V("re"),Call("Icc",Call("leftLine",Add(V("n"),Num(1))),Call("leftLine",V("n")))))));
    private static Formula Factorization() => Parameters(All("n",N,All("s",Cx,
        Imp(And(Strip(V("s")),Seq(V("s"),Neq,Sp,Negate(V("n")))),Equal(KAt(V("s")),Div(NAt(V("s")),Sub(V("s"),Negate(V("n")))))))));
    private static Formula Residue() => Parameters(Imp(Nonzero(V("z")),All("n",N,
        Equal(NAt(Negate(V("n"))),Div(Pow(V("z"),V("n")),Call("RealGamma",Add(Mul(V("alpha"),V("n")),V("beta"))))))));
    private static Formula GammaFactor(Formula c) => Div(Mul(Div(Mul(Num(2),Seq(Pi,Sp)),Abs(Call("sin",Mul(Seq(Pi,Sp),c)))),Call("exp",Negate(Mul(c,Call("log",Norm(V("z"))))))),Call("RealGamma",Sub(V("beta"),Mul(V("alpha"),c))));
    private static Formula Decay(Formula y) => Call("exp",Negate(Mul(Call("margin",V("alpha"),V("z")),Abs(y))));
    private static Formula GammaLineBound() => Parameters(All("c",R,Imp(And(Lt(Num(0),V("alpha")),And(Nonzero(Call("sin",Mul(Seq(Pi,Sp),V("c")))),Leq(Div(Num(1),Num(2)),Sub(V("beta"),Mul(V("alpha"),V("c")))))),
        All("y",R,Leq(Norm(KAt(Add(V("c"),Mul(V("y"),Imaginary)))),Mul(GammaFactor(V("c")),Decay(V("y"))))))));
    private static Formula IntegralLineBound()
    {
        Formula c=Call("leftLine",V("n"));
        Formula hypotheses=And(Lt(Num(0),V("alpha")),And(Lt(Num(0),Call("margin",V("alpha"),V("z"))),Leq(Div(Num(1),Num(2)),Sub(V("beta"),Mul(V("alpha"),c)))));
        Formula factor=Div(Mul(Mul(Num(2),Seq(Pi,Sp)),Call("exp",Negate(Mul(c,Call("log",Norm(V("z"))))))),Call("RealGamma",Sub(V("beta"),Mul(V("alpha"),c))));
        return Parameters(All("n",N,Imp(hypotheses,Leq(Norm(Call("integral",Line(c))),Mul(factor,Call("integral",Map("y",R,Decay(V("y")))))))));
    }
    private static Formula HorizontalLimits()
    {
        Formula f=Map("T",R,Call("intervalIntegral",Map("x",R,KAt(Add(V("x"),Mul(V("T"),Imaginary)))),V("a"),V("b")));
        Formula hypotheses=And(Lt(Num(0),V("alpha")),And(Leq(V("a"),V("b")),Lt(Num(0),Call("margin",V("alpha"),V("z")))));
        return Parameters(All("a",R,All("b",R,Imp(hypotheses,And(Limit(f,"atTop"),Limit(f,"atBot"))))));
    }

    private static Formula KernelFormula() => All("alpha", R, All("beta", R, All("z", Cx,
        All("s", Cx, Equal(Call("kernel", V("alpha"), V("beta"), V("z"), V("s")),
        Mul(Mul(Mul(Call("ComplexGamma", V("s")), Call("ComplexGamma", Sub(Num(1), V("s")))),
            Div(Num(1), Call("ComplexGamma", Sub(V("beta"), Mul(V("alpha"), V("s")))))),
            Call("exp", Mul(Negate(V("s")), Call("log", Negate(V("z")))))))))));
    private static Formula Params(Formula conclusion) => All("alpha", R,
        Imp(Lt(Num(0), V("alpha")), All("beta", R, All("c", R, All("z", Cx,
            Imp(Seq(Call("sin", Mul(Seq(Pi, Sp), V("c"))), Neq, Sp, Num(0)), conclusion))))));
    private static Formula MajorantFormula() => Params(Some("C", R, Some("K", N,
        All("y", R, Leq(Norm(Call("kernel", V("alpha"), V("beta"), V("z"), Add(V("c"), Mul(V("y"), Seq(Operatorname, Grp(F.Id("ComplexI"))))))),
            Mul(Mul(V("C"), Pow(Add(Num(1), Abs(V("y"))), V("K"))),
                Call("exp", Negate(Mul(Call("margin", V("alpha"), V("z")), Abs(V("y")))))))))));
    private static Formula IntegrableFormula() => Params(Imp(Lt(Num(0), Call("margin", V("alpha"), V("z"))),
        Call("Integrable", Map("y", R, Call("kernel", V("alpha"), V("beta"), V("z"), Add(V("c"), Mul(V("y"), Seq(Operatorname, Grp(F.Id("ComplexI"))))))))));

    private static Formula R => F.Id("Real");
    private static Formula Cx => F.Id("Complex");
    private static Formula N => F.Id("Nat");
    private static Formula V(string name) => F.Id(name);
    private static Formula Num(byte digit) => D(digit);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Map(string name, Formula type, Formula value) =>
        Seq(Open, F.Id(name), Colon, type, Sp, Mapsto, Sp, value, Close);
    private static Formula Add(Formula a, Formula b) => Seq(Open, a, Plus, b, Close);
    private static Formula Sub(Formula a, Formula b) => Seq(Open, a, Minus, b, Close);
    private static Formula Mul(Formula a, Formula b) => Seq(Open, a, Star, b, Close);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Negate(Formula a) => Seq(Minus, Open, a, Close);
    private static Formula Abs(Formula a) => new Formula.Absolute(a);
    private static Formula Norm(Formula a) => new Formula.Norm(a);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
