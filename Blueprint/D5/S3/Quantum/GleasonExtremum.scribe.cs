using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;
internal sealed class GleasonExtremumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Extrema without frame-function continuity", H("Extrema without frame-function continuity"), Blocks(
            Describe.Lean(DescribeId.Create("main-result"),
                DeclarationHandle.Create("D5/S3/Quantum/GleasonExtremum.exists_forall_le"),
                H("Extrema without frame-function continuity"), StatementSource.FromAuthor(Disp(MainFormula())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/gleason1957measures")),
                Blocks(Paragraph(Text("The adopted elementary real core (Sphere through General) follows Cooke, Keane, Moran (1985), Math. Proc. Cambridge Philos. Soc. 98, 117–128. The extremum argument is attributed to section 6.")),
                    Paragraph(Text("A frame function of arbitrary real weight, bounded above by M and below by m on the unit sphere, attains its maximum at a unit vector p. Applying this statement to the negative function also gives a minimum. Neither extremum statement assumes continuity or measurability of the frame function.")),
                    Paragraph(Text("A maximizing sequence has a limiting pole on the compact sphere. This fact alone cannot pass the function values to the pole. Moving orthogonal frames and symmetrization instead create a family of bounded frame functions. A cluster point in the product of closed bounded intervals retains every frame equation because each equation is closed in finitely many coordinates.")),
                    Paragraph(Text("The latitude rigidity result applies to the limiting symmetrized function. If the value at the limiting pole were strictly below the supremum, a chosen positive gap and two descent steps would contradict the inequalities along the moving frames. This proves attainment without an illicit continuity argument.")),
                    Paragraph(Text("The minimum is used to select an axis orthogonal to a maximizing direction in the real quadratic representation. Extremum attainment also applies to the residual frame function after subtracting a diagonal quadratic candidate."))), DescribeRole.Theorem))));
    private static Formula MainFormula() => All(Imp(And(Frame(), And(OnSphere(LE(Val("u"), X("M")), "u"), OnSphere(LE(X("m"), Val("u")), "u"))), Ex(And(Unit(X("p")), OnSphere(LE(Val("u"), Val("p")), "u")), ("p", V()))), ("f", Fn()), ("W", R()), ("M", R()), ("m", R()));

    private static Formula X(string x) => DefinitionDsl.Id(x);
    private static Formula C(string f, params Formula[] xs) => DefinitionDsl.Call(f, xs);
    private static Formula App(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula Eq(Formula a, Formula b) => DefinitionDsl.Equal(a, b);
    private static Formula LE(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
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
    private static Formula V() => C("EuclideanSpace", R(), C("Fin", Num(3)));
    private static Formula Fn() => new Formula.TypeArrow(V(), R());
    private static Formula Unit(Formula x) => Eq(C("norm", x), Num(1));
    private static Formula Val(string x) => App(X("f"), X(x));
    private static Formula Frame() => C("IsFrameFunction", R(), X("f"), X("W"));
    private static Formula OnSphere(Formula body, string x = "x") => All(Imp(Unit(X(x)), body), (x, V()));
}
