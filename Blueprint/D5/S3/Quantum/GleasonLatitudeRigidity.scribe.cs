using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;
internal sealed class GleasonLatitudeRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rigidity of simple frame functions", H("Rigidity of simple frame functions"), Blocks(
            Describe.Lean(DescribeId.Create("main-result"),
                DeclarationHandle.Create("D5/S3/Quantum/GleasonLatitudeRigidity.eq_add_mul_latitude"),
                H("Rigidity of simple frame functions"), StatementSource.FromAuthor(Disp(MainFormula())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/gleason1957measures")),
                Blocks(Paragraph(Text("Let f be a real frame function of arbitrary weight W on all orthonormal bases of real three-space. Suppose a unit vector p is a global maximum on the sphere and f has the constant value m on the equator perpendicular to p. Then f at every unit vector s equals m plus the difference f(p) minus m times the latitude of s.")),
                    Paragraph(Text("The frame identity makes equatorial points global minima. A four-point identity makes f monotone along every descent, and finite geometric descent makes it monotone in latitude. Suprema and infima along a fixed latitude can differ at only countably many latitude values.")),
                    Paragraph(Text("Outside those exceptional latitudes, a one-dimensional frame sum and monotonicity determine the value. Rational multiples of one latitude are chosen to avoid the countable exceptional set; rational squeezing then fixes the linear slope. Approaching an exceptional latitude from both sides proves the same value there.")),
                    Paragraph(Text("The bounded additive step uses continuity of an additive homomorphism bounded on a neighbourhood of zero, followed by real scalar linearity. Continuity is derived for that additive homomorphism; it is never imposed on f. All statements quantify over functions and real parameters rather than over a finite list of numerical examples."))), DescribeRole.Theorem))));
    private static Formula MainFormula() => All(Imp(And(Frame(), And(Unit(X("p")), And(OnSphere(LE(Val("x"), Val("p"))), All(Imp(C("equator", X("p"), X("e")), Eq(Val("e"), X("m"))), ("e", V()))))), OnSphere(Eq(Val("s"), Add(X("m"), Multiply(Subtract(Val("p"), X("m")), C("latitude", X("p"), X("s"))))), "s")), ("f", Fn()), ("W", R()), ("p", V()), ("m", R()));

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
    private static Formula R() => X("R");
    private static Formula V() => C("EuclideanSpace", R(), C("Fin", Num(3)));
    private static Formula Fn() => new Formula.TypeArrow(V(), R());
    private static Formula Unit(Formula x) => Eq(C("norm", x), Num(1));
    private static Formula Val(string x) => App(X("f"), X(x));
    private static Formula Frame() => C("IsFrameFunction", R(), X("f"), X("W"));
    private static Formula OnSphere(Formula body, string x = "x") => All(Imp(Unit(X(x)), body), (x, V()));
}
