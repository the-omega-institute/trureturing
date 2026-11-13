using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;
internal sealed class GleasonComplexRepresentationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite complex projection Gleason representation", H("Finite complex projection Gleason representation"), Blocks(
            Describe.Lean(DescribeId.Create("main-result"),
                DeclarationHandle.Create("D5/S3/Quantum/GleasonComplexRepresentation.gleason_representation"),
                H("Finite complex projection Gleason representation"), StatementSource.FromAuthor(Disp(MainFormula())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/gleason1957measures")),
                Blocks(Paragraph(Text("Gleason (1957), J. Math. Mech. 6, 885, Theorems 2.8 and 3.1, is the projection-theorem source. the adopted elementary real core (Sphere through General) follows Cooke, Keane, Moran (1985), Math. Proc. Cambridge Philos. Soc. 98, 117–128.")),
                    Paragraph(Text("For every natural dimension N at least three and every projection package OP on complex N by N matrices, there is exactly one matrix rho that is positive semidefinite, has trace one, and satisfies OP.p(P) = Re(trace(rho P)) for every star projection P. The package is a total matrix function, constrained only by nonnegative projection values, normalization at the identity and binary additivity on orthogonal star projections.")),
                    Paragraph(Text("Restrict the rank-one frame function to every completely real orthonormal triple. The real sphere theorem gives a quadratic restriction there. Extending each real orthonormal pair to such a triple gives real-plane regularity. Comparing rotated pairs shows the cross term depends linearly on the real and imaginary parts of a unit phase.")),
                    Paragraph(Text("The homogeneous extension of the frame function to all vectors satisfies the parallelogram law. Integer quadratic polarization and bounded additive real linearity yield a sesquilinear form. Its standard-basis matrix is Hermitian and has the original function as its diagonal quadratic form. Mixed real scalar identities are derived in this construction, rather than assumed.")),
                    Paragraph(Text("Sphere positivity gives positive semidefiniteness, and the standard orthonormal frame sum gives trace one. Spectral resolution of a star projection has eigenvalues zero or one, so finite orthogonal additivity extends the rank-one formula to every projection. Equality on all rank-one projections determines the matrix, proving uniqueness.")),
                    Paragraph(Text("Projective noncontextuality and the all-projections domain are mathematical premises. The theorem does not derive them empirically. It treats finite complex matrices only; the separable infinite-dimensional theorem, countable additivity, trace-class operators and an infinite-dimensional trace-one conclusion require additional results."))), DescribeRole.Theorem))));
    private static Formula MainFormula() => All(Imp(LE(Num(3), X("N")), Ex(And(Law(X("rho")), All(Imp(Law(X("sigma")), Eq(X("sigma"), X("rho"))), ("sigma", Mat()))), ("rho", Mat()))), ("N", X("Nat")), ("OP", C("ProjectionPackage", X("N"))));

    private static Formula X(string x) => DefinitionDsl.Id(x);
    private static Formula C(string f, params Formula[] xs) => DefinitionDsl.Call(f, xs);
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
    private static Formula Mat() => C("Matrix", C("Fin", X("N")), C("Fin", X("N")), X("C"));
    private static Formula Law(Formula rho) => And(C("PosSemidef", rho), And(Eq(C("trace", rho), Num(1)), All(Imp(C("IsStarProjection", X("P")), Eq(C("p", X("OP"), X("P")), C("Re", C("trace", Multiply(rho, X("P")))))), ("P", Mat()))));
}
