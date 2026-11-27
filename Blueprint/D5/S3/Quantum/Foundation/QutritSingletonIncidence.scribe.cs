using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class QutritSingletonIncidenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A shared original pure ray determines the homogeneous intersection of actual qutrits.",
        H("Singleton incidence of actual qutrit faces"), Blocks(
            Describe.Lean(DescribeId.Create("original-qutrit-singleton-incidence"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/QutritSingletonIncidence.original_qutrit_singleton_incidence"),
                H("The homogeneous intersection is one real line"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/meiburg2026ssa")),
                Blocks(
                    Paragraph(Text("Let C be a pointed cone in a finite-dimensional real normed vector space V. The real-linear unit u is strictly positive on every nonzero element of C. Original pure states are extreme points of the full u = 1 base, and wholePairBalls supplies the original pair-ball charts. The actual faces H and J admit real-linear coordinates on their entire homogeneous spans identifying their cones with the three-by-three complex Hermitian positive semidefinite cone and their units with the trace. The nonnegative linear support g exposes H, and the intersection of the two faces consists exactly of the nonnegative multiples of an original pure state p.")),
                    Paragraph(Text("In J, the positive Hermitian representative of g has exactly one zero eigenvalue. Its trace-one zero-support pivot maps to p. On the remaining two coordinates the weights of the diagonal support are strictly positive. A common-span matrix has weighted complementary diagonal sum zero. The complementary two-by-two determinant is nonpositive. If it is zero, the complementary block vanishes and the matrix is already singular. Otherwise a real multiple of the pivot cancels the three-by-three determinant by its affine dependence on the pivot entry. In both cases the shifted matrix remains in the common span.")),
                    Paragraph(Text("A singular Hermitian three-by-three matrix has at most two nonzero spectral atoms. QutritSchurPlane.unit_rankOne_original lifts their unit-normalized rank-one projectors to original pure states. The atoms of zero support lie on p. When both supports are positive, the zero total support allows the atoms to be scaled to support one and their quotient images agree. QutritPureLift.unique_original_pure_lift forces their equality and hence cancellation. Subtracting the pivot shift proves that every common-span vector belongs to the real line of p.")),
                    Paragraph(Text("This supplies singleton incidence in the local carrier-dimension sixteen through eighteen arguments. The global carrier-dimension conclusions require the remaining incidence and dimension arguments."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula In(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula App(Formula a, Formula b) => new Formula.Apply(a, [b]);

    private static Formula Statement()
    {
        var real = Seq(Mathbb, Grp(F.Id("R")));
        var complex = Seq(Mathbb, Grp(F.Id("C")));
        var v = F.Id("V");
        var cone = F.Id("C");
        var h = F.Id("H");
        var j = F.Id("J");
        var p = F.Id("p");
        var u = F.Id("u");
        var g = F.Id("g");
        var eH = F.Id("eH");
        var eJ = F.Id("eJ");
        var x = F.Id("x");
        var a = F.Id("a");
        var hermitian = Call("HermitianMat", Call("Fin", D(3)), complex);
        Formula Span(Formula face) => Call("span", real, face);
        Formula Chart(Formula face) => Call("LinearEquiv", real, Span(face), hermitian);
        Formula Coordinates(Formula face, Formula e) => All("x", Span(face), And(
            new Formula.Logic(In(Call("val", x), face), FormulaLogicOperator.Iff, Le(D(0), App(e, x))),
            Eq(Call("trace", App(e, x)), App(u, Call("val", x)))));
        var strict = All("x", v, Imp(And(In(x, cone), new Formula.Not(Eq(x, D(0)))), Lt(D(0), App(u, x))));
        var support = All("x", v, Imp(In(x, cone), And(Le(D(0), App(g, x)),
            new Formula.Logic(Eq(App(g, x), D(0)), FormulaLogicOperator.Iff, In(x, h)))));
        var incidence = All("x", v, new Formula.Logic(And(In(x, h), In(x, j)), FormulaLogicOperator.Iff,
            Ex("a", real, And(Le(D(0), a), Eq(x, Call("smul", a, Call("val", p)))))));
        var hypotheses = And(strict, And(support, And(Call("wholePairBalls", cone, u),
            And(incidence, And(Coordinates(h, eH), Coordinates(j, eJ))))));
        var result = Eq(Call("inf", Span(h), Span(j)), Span(Call("singleton", Call("val", p))));
        var lin = Call("LinearMap", real, v, real);
        var faceType = Call("Face", cone);
        return All("V", F.Id("Type"), Seq(OpenBracket, Call("NormedAddCommGroup", v), CloseBracket, Sp,
            OpenBracket, Call("NormedSpace", real, v), CloseBracket, Sp,
            OpenBracket, Call("FiniteDimensional", real, v), CloseBracket, Sp,
            All("C", Call("PointedCone", real, v), All("u", lin, All("g", lin,
                All("H", faceType, All("J", faceType, All("p", Call("pure", cone, u),
                    All("eH", Chart(h), All("eJ", Chart(j), Imp(hypotheses, result)))))))))));
    }
}
