using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class OpenBoundaryMPSInteriorPolynomialDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorPolynomial";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual interior polynomial transversality in eighteen real coordinates", H("Actual interior polynomial transversality in eighteen real coordinates"), Blocks(
            Describe.Lean(DescribeId.Create("openboundarympsinteriorpolynomial-polynomial-clear"),
                DeclarationHandle.Create(Module + ".polynomial_clear"), H("Literal independent-trial real polynomials"),
                StatementSource.FromAuthor(Disp(ClearFormula())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Construct the exact native core at the actual target z0 in paired complex polynomial variables. Forward left and right recurrences form the actual target matrices. The central G(z0) squared congruence is outside the right transfer iterate. The division-free adjugate and Schur recurrences then vary only the independent trial z. Cartesian conversion, real coefficient extraction and explicit reindexing give FL_pq and FR_pq over the real numbers in trial x,y plus sixteen actual coordinates. Their exact evaluations are cL times the real native residual and cR times its imaginary component."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("openboundarympsinteriorpolynomial-b-eval-derivative"),
                DeclarationHandle.Create(Module + ".b_eval_derivative"), H("Differentiate trial variables before target substitution"),
                StatementSource.FromAuthor(Disp(DerivativeFormula())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The actual coordinate order is lambda.re,lambda.im,mu.re,mu.im,a.re,a.im,l0.re,l0.im,l1.re,l1.im,r0.re,r0.im,r1.re,r1.im,z0.re,z0.im. First form the formal trial determinant pderiv_x(FL) pderiv_y(FR)-pderiv_y(FL) pderiv_x(FR), then substitute x=z0.re,y=z0.im. This defines b_pq in sixteen real actual variables. At the native common root, for any ordinary real derivative D of the fixed-target residual, eval(b_pq)=cL(z0)cR(z0)det_R(D). The diagonal identity in changing target parameters is never differentiated."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("openboundarympsinteriorpolynomial-b-nonzero"),
                DeclarationHandle.Create(Module + ".b_nonzero"), H("All positive exterior lengths have a nonzero polynomial"),
                StatementSource.FromAuthor(Disp(NonzeroFormula())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every p,q at least one, consume interior_q2_fixed_target_witness from the authoritative native transversality module, at sector (2,0,1), l=(1,1), r=(1,I), z0=1. Its real triangular derivative has nonzero determinant. The exact Jacobian identity and the strictly positive factors prove nonzero evaluation at this actual witness and hence b_pq is not the zero polynomial. There is no added witness, derivative invertibility or nonzero premise."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("openboundarympsinteriorpolynomial-b-right-scale"),
                DeclarationHandle.Create(Module + ".b_right_scale"), H("Right-boundary amplitude restoration"),
                StatementSource.FromAuthor(Disp(ScaleFormula())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every real a, replacing the actual right boundary r by a r multiplies its outer Gram and target quadratically. The full cleared right recurrence remains linear in this target, so its determinant row and the corresponding trial derivatives scale by a^4. The left row and both clearing factors are unchanged. Thus eval(b_pq) scales by exactly a^4, including a=0. This is the amplitude transport needed when a subsequent finite spectral descent extracts a dyadic boundary and restores a square-root amplitude. The derivative here has two real inputs and two real outputs. Spectral coefficient rank four is a separate algebraic notion."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("openboundarympsinteriorpolynomial-nonzero-locus-actual-ambiguity"),
                DeclarationHandle.Create(Module + ".nonzero_locus_actual_ambiguity"), H("Actual annular ambiguity on the nonzero locus"),
                StatementSource.FromAuthor(Disp(AmbiguityFormula())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("On a regular sector with nonzero actual z0 and positive definite actual left and right environments, nonzero evaluation of b yields an invertible ordinary real derivative. Differentiability follows from the literal polynomial slices divided by the nonzero clearing factors on a neighborhood of z0. The endpoint-sign supplier produces radii enclosing z0 with a negative first residual component on both entire circles. The native annular root-realization theorem then constructs a nonzero actual finite MPS with identical entire rawInterior p 2 q and no unit-phase relation to the target. Positive actual environments remain hypotheses."))), DescribeRole.Theorem),
            Paragraph(Text("These are parameter-locus statements for finite native unnormalized MPS observations. Canonical chart dominance, genericity on actual full-state or actual raw-density images, and the full Critch-Morton C9 problem remain separate obligations. No solved-open-problem credit, clock, dynamics, energy, positive physical inverse or thermodynamic cost follows.")))));

    private static Formula AmbiguityFormula()
    {
        var p=Id("p"); var q=Id("q"); var n=Add(Add(p,D(2)),q); var zo=Id("zo");
        var state=Call("mpsState",n,Call("core",Id("s"),zo,D(0)),Call("core",Id("s"),zo,D(1)),Id("l"),Id("r"));
        var phi=Id("phi"); var eta=Id("eta");
        var conclusion=Some("phi",Call("Function",Call("Word",n),Id("Complex")),And(
            Call("Member",phi,Call("openBoundaryMPS",n)),Ne(phi,D(0)),
            Eq(Call("rawInterior",p,D(2),q,phi),Call("rawInterior",p,D(2),q,state)),
            Seq(Neg,Sp,Par(Some("eta",Id("Complex"),And(Eq(Call("norm",eta),D(1)),Eq(phi,Call("smul",eta,state))))))));
        return Bind(ActualBinders,Imp(And(Le(D(1),p),Le(D(1),q),Call("Regular",Id("s")),Ne(zo,D(0)),
            Call("PosDef",Call("leftTarget",Id("s"),zo,Id("l"),p)),Call("PosDef",Call("rightTarget",Id("s"),zo,Id("r"),q)),
            Ne(Call("eval",Target,Call("b",p,q)),D(0))),conclusion));
    }
    private static Formula Target => Call("coordinates",Id("s"),Id("l"),Id("r"),Id("zo"));
    private static Formula Native => Call("residual",Id("s"),Id("p"),Id("q"),Call("leftTarget",Id("s"),Id("zo"),Id("l"),Id("p")),Call("rightTarget",Id("s"),Id("zo"),Id("r"),Id("q")));
    private static (string Name, Formula Type)[] ActualBinders => [("p",Id("Nat")),("q",Id("Nat")),("s",Id("Sector")),("l",Call("Function",Call("Fin",D(2)),Id("Complex"))),("r",Call("Function",Call("Fin",D(2)),Id("Complex"))),("zo",Id("Complex"))];
    private static Formula ClearFormula()
    {
        var z=Id("z");
        return Bind(ActualBinders,Imp(Call("Regular",Id("s")),All("z",Id("Complex"),Imp(Ne(z,D(0)),And(
            Eq(Call("eval",Call("slice",Target,z),Call("FL",Id("p"),Id("q"))),Mul(Call("cL",Id("s"),Id("p"),z),Call("re",Call("apply",Native,z)))),
            Eq(Call("eval",Call("slice",Target,z),Call("FR",Id("p"),Id("q"))),Mul(Call("cR",Id("s"),Id("q"),z),Call("im",Call("apply",Native,z)))))))));
    }
    private static Formula DerivativeFormula() => Bind(ActualBinders,Imp(And(Call("Regular",Id("s")),Ne(Id("zo"),D(0))),
        All("D",Call("RealContinuousLinearEnd",Id("Complex")),Imp(Call("HasFDerivAt",Native,Id("D"),Id("zo")),
            Eq(Call("eval",Target,Call("b",Id("p"),Id("q"))),Mul(Mul(Call("cL",Id("s"),Id("p"),Id("zo")),Call("cR",Id("s"),Id("q"),Id("zo"))),Call("det",Call("toLinearMap",Id("D")))))))));
    private static Formula NonzeroFormula() => Bind([("p",Id("Nat")),("q",Id("Nat"))],Imp(And(Le(D(1),Id("p")),Le(D(1),Id("q"))),And(
        Ne(Call("eval",Call("coordinates",Id("fixedSector"),Id("leftBoundary"),Id("rightBoundary"),D(1)),Call("b",Id("p"),Id("q"))),D(0)),Ne(Call("b",Id("p"),Id("q")),D(0)))));
    private static Formula ScaleFormula() => Bind([("p",Id("Nat")),("q",Id("Nat")),("theta",Call("Function",Call("Fin",D(1,6)),Id("Real"))),("a",Id("Real"))],
        Eq(Call("eval",Call("scaleRight",Id("a"),Id("theta")),Call("b",Id("p"),Id("q"))),Mul(Pow(Id("a"),D(4)),Call("eval",Id("theta"),Call("b",Id("p"),Id("q"))))));

    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Id(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Some(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula Bind((string Name, Formula Type)[] xs, Formula b) { for (var i = xs.Length - 1; i >= 0; --i) b = All(xs[i].Name, xs[i].Type, b); return b; }
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula And(params Formula[] xs) => xs.Aggregate((a, b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b)));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
}
