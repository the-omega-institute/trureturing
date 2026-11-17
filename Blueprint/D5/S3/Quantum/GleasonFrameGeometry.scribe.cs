using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;
internal sealed class GleasonFrameGeometryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite descent on the real sphere", H("Finite descent on the real sphere"), Blocks(
            Describe.Lean(DescribeId.Create("main-result"),
                DeclarationHandle.Create("D5/S3/Quantum/GleasonFrameGeometry.exists_descent_chain"),
                H("Finite descent on the real sphere"), StatementSource.FromAuthor(Disp(MainFormula())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/gleason1957measures")),
                Blocks(Paragraph(Text("The adopted elementary real core (Sphere through General) follows Cooke, Keane, Moran (1985), Math. Proc. Cambridge Philos. Soc. 98, 117–128.")),
                    Paragraph(Text("The ambient space is real Euclidean three-space. A unit pole p determines its northern closed hemisphere, the unit vectors s with nonnegative inner product with p. Latitude is the square of that inner product. A descent step stays on the great circle orthogonal to the coldest equatorial direction associated with its starting point.")),
                    Paragraph(Text("For two northern unit vectors distinct from the pole, strictly decreasing latitude is realized by a finite descent chain. IsDescentChain records both endpoints, membership of every indexed vector in the northern hemisphere away from the pole, and the descent relation at every successive index. The natural number n is at least one.")),
                    Paragraph(Text("The construction lifts tangent coordinates to the sphere. A complex spiral rotates the tangent direction while increasing its radius; a cosine estimate selects a finite number of steps. Two additional ray steps correct the endpoint. No property or continuity of a frame function enters this geometric construction.")),
                    Paragraph(Text("A projection package is a total real-valued function on complex square matrices. Only star projections are constrained: nonnegative values, value one at the identity and binary additivity when the projection product is zero. Rank-one projection values therefore sum to one on every orthonormal basis. The associated real frame identity is a sum of three values on each orthonormal triple."))), DescribeRole.Theorem))));
    private static Formula MainFormula() => All(Imp(And(Unit(X("p")), And(C("northern", X("p"), X("s")), And(new Formula.Not(Eq(X("s"), X("p"))), And(C("northern", X("p"), X("t")), And(new Formula.Not(Eq(X("t"), X("p"))), LT(C("latitude", X("p"), X("t")), C("latitude", X("p"), X("s")))))))), Ex(And(LE(Num(1), X("n")), C("IsDescentChain", X("p"), X("s"), X("t"), X("n"), X("c"))), ("n", X("Nat")), ("c", new Formula.TypeArrow(X("Nat"), V())))), ("p", V()), ("s", V()), ("t", V()));

    private static Formula X(string x) => DefinitionDsl.Id(x);
    private static Formula C(string f, params Formula[] xs) => DefinitionDsl.Call(f, xs);
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
    private static Formula V() => C("EuclideanSpace", R(), C("Fin", Num(3)));
    private static Formula Unit(Formula x) => Eq(C("norm", x), Num(1));

}
