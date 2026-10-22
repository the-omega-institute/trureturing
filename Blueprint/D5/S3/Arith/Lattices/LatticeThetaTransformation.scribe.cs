using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices;

internal sealed class LatticeThetaTransformationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For actual LatticeData D, assume its real Gram matrix is positive definite, its integral Gram determinant is a unit, and its rank equals m+m for a natural m. For every complex tau with positive imaginary part, the ordinary charge theta terms have summable norms and latticeTheta D (-1/tau)=(-i tau)^m latticeTheta D tau. The integer Gram matrix acts bijectively on charges, with its integral matrix inverse providing the inverse map. This reindexes the inverse-form theta series; positivity and integral unimodularity give determinant one. Rank zero is included. This theta identity does not identify any operator trace or oscillator factor.",
        H("LatticeThetaTransformation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("theta-inverse-integer-reindex"),
                DeclarationHandle.Create("D5/S3/Arith/Lattices/LatticeThetaTransformation.theta_inverse_integer_reindex"),
                H("Integer inverse-form reindexing"),
                StatementSource.FromAuthor(ReindexFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural rank r, integer matrix G whose real extension is positive definite, unit integral determinant and complex tau, the theta series of the inverse real Gram equals the theta series of the real Gram. Multiplication by G is a bijection of the full integer coordinate space, with inverse multiplication by the integral matrix inverse. The quadratic identity follows from actual matrix inverse cancellation. Evenness and positive rank are not required for this reindexing."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticethetatransformation-latticetheta"),
                DeclarationHandle.Create("D5/S3/Arith/Lattices/LatticeThetaTransformation.latticeTheta"),
                H("The ordinary integral-charge theta series"),
                StatementSource.FromAuthor(ThetaFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For actual LatticeData D, latticeTheta D tau sums exp(pi i tau bilinear_D(a,a)) over every integer charge a. This is the ordinary charge sum."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticethetatransformation-lattice-theta-s"),
                DeclarationHandle.Create("D5/S3/Arith/Lattices/LatticeThetaTransformation.lattice_theta_S"),
                H("The even-unimodular lattice S law"),
                StatementSource.FromAuthor(SFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For actual LatticeData D, assume its real Gram matrix is positive definite, its integral Gram determinant is a unit, and its rank equals m+m for a natural m. For every complex tau with positive imaginary part, the ordinary charge theta terms have summable norms and latticeTheta D (-1/tau)=(-i tau)^m latticeTheta D tau. The integer Gram matrix acts bijectively on charges, with its integral matrix inverse providing the inverse map. This reindexes the inverse-form theta series; positivity and integral unimodularity give determinant one. Rank zero is included. This theta identity does not identify any operator trace or oscillator factor."))),
                DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula Imag => Seq(Operatorname, Grp(V("Complex")), Dot, Operatorname, Grp(V("I")));
    private static Formula C => Seq(Mathbb, Grp(V("C")));
    private static Formula Z => Seq(Mathbb, Grp(V("Z")));
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula All(string s, Formula t, Formula p) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, p);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Pos(Formula a) => new Formula.Relation(D(0), FormulaRelationOperator.LessThan, a);
    private static Formula Mul(Formula a, Formula b) => Multiply(a, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula NegF(Formula a) => new Formula.Negate(a);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Inv(Formula a) => Pow(a, NegF(D(1)));
    private static Formula Cast(Formula a, Formula t) => Seq(Open, a, Colon, t, Close);
    private static Formula Lam(string s, Formula t, Formula p) => Seq(Open, V(s), Colon, t, Sp, Mapsto, Sp, p, Close);
    private static Formula Norm(Formula x) => new Formula.Norm(x);
    private static Formula ExpF(Formula x) => Call("exp", x);
    private static Formula FinR => Call("Fin", V("r"));
    private static Formula Mat(Formula n, Formula t) => Call("Matrix", n, n, t);
    private static Formula Tsum(string s, Formula t, Formula p) => Call("tsum", Lam(s, t, p));
    private static Formula Summable(string s, Formula t, Formula p) => Call("Summable", Lam(s, t, p));
    private static Formula UpperParameter(Formula p) => All("tau", C, Imp(Pos(Call("im", V("tau"))), p));

    private static Formula RealGram(Formula g) => Call("map", g, Call("IntCastRingHom", R));
    private static Formula DGram => Seq(V("D"), Dot, V("G"));
    private static Formula LatticeTerm() => ExpF(Mul(Mul(Mul(Pi, Imag), V("tau")),
        Cast(Call("bilinear", V("D"), V("a"), V("a")), C)));
    private static Formula ThetaFormula() => Disp(All("D", V("LatticeData"), All("tau", C,
        Equal(Call("latticeTheta", V("D"), V("tau")), Tsum("a", Call("Charge", V("D")), LatticeTerm())))));
    private static Formula ReindexFormula() => Disp(All("r", N, All("G", Mat(FinR, Z),
        Imp(And(Call("PosDef", RealGram(V("G"))), Call("IsUnit", Call("det", V("G")))),
            All("tau", C, Equal(Call("theta", Inv(RealGram(V("G"))), V("tau")),
                Call("theta", RealGram(V("G")), V("tau"))))))));
    private static Formula SFormula() => Disp(All("D", V("LatticeData"),
        Imp(And(Call("PosDef", RealGram(DGram)), Call("IsUnit", Call("det", DGram))),
            All("m", N, Imp(Equal(Call("rank", V("D")), Add(V("m"), V("m"))), UpperParameter(
                And(Summable("a", Call("Charge", V("D")), Norm(LatticeTerm())),
                    Equal(Call("latticeTheta", V("D"), Div(NegF(D(1)), V("tau"))),
                        Mul(Pow(Mul(NegF(Imag), V("tau")), V("m")),
                            Call("latticeTheta", V("D"), V("tau")))))))))));
}
