using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class UnitBridgeRawGeometryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coordinate recovery and output normality for a total skew relation on the original continuous spin sections.",
        H("The original continuous spin carrier"),
        Blocks(
            Paragraph(Text("A section is represented by its four continuous real coordinate functions, with coordinate zero along the unit and coordinates one through three along the fixed orthonormal axes. This is the coordinate presentation of C(T, R u plus R^3). The source norm is the supremum of abs(alpha) plus sqrt(x1^2+x2^2+x3^2), and the positive cone is alpha >= sqrt(x1^2+x2^2+x3^2) pointwise. The auxiliary energy alpha^2+x1^2+x2^2+x3^2 used below is a different quadratic expression, not a replacement norm.")),
            Paragraph(Text("Original(T) consists of a real linear subspace E closed under the specified spin Jordan product and containing every constant four-coordinate section. The coefficient algebra A is exactly the continuous functions f whose central section (f,0,0,0) belongs to E. No density, completeness, inverse closure or square-root closure is imposed. The algebraic statements hold for every topological T, hence in particular for the nonempty compact Hausdorff source domain.")),
            Describe.Lean(
                DescribeId.Create("original-four-components"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/UnitBridgeRawGeometry.original_four_components"),
                H("All four coefficients belong to the actual coefficient algebra"),
                StatementSource.FromAuthor(F.Disp(All("T", Id("TopologicalSpaces"), All("E", Call("Original", Id("T")),
                    All("a", Call("Sections", Id("T")), Iff(Call("mem", Id("a"), Call("carrier", Id("E"))),
                        All("i", Call("Fin", Num(4)), Call("mem", Call("a", Id("i")), Call("scalarAlgebra", Id("E"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Twice multiplying by an axis gives the projection onto the unit and that axis. Half the sum of the three such projections minus the original section isolates the scalar component. Subtract it from each axis projection and multiply by that axis to recover each vector coefficient along the unit. Conversely, Jordan multiplication of each central coefficient by the corresponding constant axis reconstructs the section. Uniqueness follows from equality of the four coordinate functions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("raw-output-normal"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/UnitBridgeRawGeometry.raw_output_normal"),
                H("Two raw moments force pointwise normality"),
                StatementSource.FromAuthor(F.Disp(All("T", Id("TopologicalSpaces"), All("E", Call("Original", Id("T")),
                    All("R", Call("Raw", Id("E")), All("a", Call("Elem", Id("E")), All("b", Call("Elem", Id("E")),
                        All("t", Id("T"), And(Equal(Call("scalarAt", Call("D", Id("R"), Id("a"), Id("b")), Id("t")), Num(0)),
                            And(Equal(Call("vectorDotAt", Id("a"), Call("D", Id("R"), Id("a"), Id("b")), Id("t")), Num(0)),
                                Equal(Call("vectorDotAt", Id("b"), Call("D", Id("R"), Id("a"), Id("b")), Id("t")), Num(0))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Raw(E) supplies the same total D:E x E -> E, skewness, the full Jordan PY identity, and D(a,D(a,b))=H_a(b). It supplies no additivity, continuity, real homogeneity, point-evaluation descent, Jacobi or associator law. Write p=D(a,b), rho=x dot x and Gamma=rho(y dot y)-(x dot y)^2. PY gives energy(p)=Gamma. PY at (a,p), followed by NN and the polynomial identity energy(H_a(b))=rho Gamma, gives rho p0^2+(x dot p)^2=0. Positivity forces x dot p=0; if rho is nonzero it also forces p0=0, while rho=0 makes Gamma and every coordinate of p zero. Skewness gives orthogonality to the other input. These statements concern actual original outputs, without defining a quotient relation at a point."))),
                DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Num(int n) => F.Num(n);
    private static Formula Call(string name, params Formula[] args) => F.Call(name, args);
    private static Formula Equal(Formula a, Formula b) => F.Equal(a,b);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
}
