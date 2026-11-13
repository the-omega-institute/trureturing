using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;
internal sealed class GleasonRealRepresentationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quadratic representation on the real sphere", H("Quadratic representation on the real sphere"), Blocks(
            Describe.Lean(DescribeId.Create("main-result"),
                DeclarationHandle.Create("D5/S3/Quantum/GleasonRealRepresentation.frameFunction_regular_sphere"),
                H("Quadratic representation on the real sphere"), StatementSource.FromAuthor(Disp(MainFormula())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/gleason1957measures")),
                Blocks(Paragraph(Text("Every real-valued function whose sum is W on every orthonormal basis of real three-space, and whose values are nonnegative on the entire unit sphere, is a symmetric quadratic form on that sphere. The weight W is arbitrary; the function outside the sphere is unrestricted. No continuity or measurability hypothesis occurs.")),
                    Paragraph(Text("Nonnegativity and the frame sum give upper bound W. Extremum attainment chooses a maximum p. Applying the minimum theorem to the sum of f and the squared inner product with p gives a minimizing direction r orthogonal to p. The cross product supplies the remaining orthogonal axis q.")),
                    Paragraph(Text("The diagonal quadratic candidate takes the values f(p), f(q) and f(r) on those axes. The difference between this candidate and f is again a frame function. Pole rotations make its values antisymmetric and force it to vanish on four great circles.")),
                    Paragraph(Text("The residual attains a maximum. The geometric half-inner-product identities and the four vanishing circles force that maximum to be zero, hence the residual vanishes everywhere on the sphere. Expanding the diagonal expression in the chosen orthonormal frame gives the symmetric real matrix."))), DescribeRole.Theorem))));
    private static Formula MainFormula() => All(Imp(And(Frame(), OnSphere(LE(Num(0), Val("x")))), Ex(And(C("IsSymm", X("A")), OnSphere(Eq(Val("x"), C("dot", X("x"), C("mulVec", X("A"), X("x")))))), ("A", C("Matrix", Num(3), Num(3), R())))), ("f", Fn()), ("W", R()));

    private static Formula X(string x) => DefinitionDsl.Id(x);
    private static Formula C(string f, params Formula[] xs) => DefinitionDsl.Call(f, xs);
    private static Formula App(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula Eq(Formula a, Formula b) => DefinitionDsl.Equal(a, b);
    private static Formula LE(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula LT(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(Formula body, params (string Name, Formula Type)[] xs)
    {
        for (var i = xs.Length - 1; i >= 0; --i)
            body = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(xs[i].Name), xs[i].Type, body);
        return body;
    }
    private static Formula Ex(Formula body, params (string Name, Formula Type)[] xs)
    {
        for (var i = xs.Length - 1; i >= 0; --i)
            body = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(xs[i].Name), xs[i].Type, body);
        return body;
    }
    private static Formula R() => X("R");
    private static Formula V() => C("EuclideanSpace", R(), Num(3));
    private static Formula Fn() => new Formula.TypeArrow(V(), R());
    private static Formula Unit(Formula x) => Eq(C("norm", x), Num(1));
    private static Formula Val(string x) => App(X("f"), X(x));
    private static Formula Frame() => C("IsFrameFunction", R(), X("f"), X("W"));
    private static Formula OnSphere(Formula body, string x = "x") => All(Imp(Unit(X(x)), body), (x, V()));
}
