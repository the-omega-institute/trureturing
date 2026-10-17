using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class LengthGramTwentySubdivisionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact twenty tetrahedra of the original positive-six-length cut body.",
        H("The literal twenty-cell subdivision in one affine hyperplane"),
        Blocks(
            Paragraph(Text("Use six independently positive lengths in the original order 01,02,03,23,13,12. The full literal array and the original endpoint and face conventions are retained in the owning LengthGramBody application. Write V(l,n) for its fourtuple, K(l,n)=convexHull(range(V(l,n))), C(l) for the original cutBody, and H={v in Real4:sum(v)=1}. Write IH(l,n) for the image in Real4 of the interior of K(l,n) as a subset of the same subtype H. iUnionFin20(K(l)) denotes the indexed union of the twenty cells. I(l,n)=intrinsicInterior_Real(K(l,n)), while interiorInH(l,n) is the interior of the preimage of K(l,n) under the inclusion of H.")),
            Describe.Lean(
                DescribeId.Create("original-twenty-tetrahedra"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/LengthGramTwentySubdivision.twenty_subdivision"),
                H("Closed cover, nondegeneracy, common span and intrinsic separation"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Supporting zero traces select the positive-weight original vertices of a convex combination. Their exact endpoint incidences give each cap triangle and each opposite side segment. Two consecutive support-ratio extensions give the original four-triangle side fans and their cones from the original barycenter. Two supports isolate the first two coefficients of an affine relation; endpoint injectivity isolates the last two. The resulting linear basis proves that every cell spans H.")),
                    Paragraph(Text("For cells on different faces use M(b)L-L(b)M. For fan cells on the same side first use M(a)L-L(a)M, then subtract its barycenter value times four times the omitted coordinate. These forms separate the two vertex sets and have an original strict endpoint witness. The exact frozen intrinsic-extension lemma turns the strict vertex witness into strictness throughout the intrinsic interior. The proved span identity identifies those interiors with interiors in the same H.")),
                    Paragraph(Text("This coefficient subdivision is separate from native-integral substitutions, local domination, native C1 regularity, Schlaefli variation and the full four-volume objective. The construction adds none of those conclusions."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var l = F.Id("l");
        var n = F.Id("n");
        var m = F.Id("m");
        var K = Call("K", l, n);
        var V = Call("V", l, n);
        return All("l", F.Id("R6"), Implies(
            All("q", Call("Fin", F.D(6)), Lt(F.D(0), Call("l", F.Id("q")))),
            And(Eq(Call("C", l), Call("iUnionFin20", Call("K", l))),
                All("n", Call("Fin", F.D(20)), And(
                    Call("IsClosed", K), Call("AffineIndependent", F.Id("Real"), V),
                    Eq(Call("affineSpan", F.Id("Real"), Call("range", V)), F.Id("H")),
                    Eq(Call("affineSpan", F.Id("Real"), K), F.Id("H")))),
                All("n", Call("Fin", F.D(20)), Eq(Call("I", l, n), Call("IH", l, n))),
                All("n", Call("Fin", F.D(20)), All("m", Call("Fin", F.D(20)),
                    Implies(Call("Distinct", n, m), And(
                        Call("Disjoint", Call("I", l, n), Call("I", l, m)),
                        Call("Disjoint", Call("interiorInH", l, n), Call("interiorInH", l, m)))))))));
    }
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula And(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
}
