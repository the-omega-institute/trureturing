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
                DescribeRole.Theorem),
            Node("raw-h-fibre", "raw_h_fibre", "Constancy on an original H fibre",
                RawScope(All("a", Elem, All("b", Elem, All("c", Elem,
                    Imp(Equal(Call("H", Id("E"), Id("a"), Id("b")), Call("H", Id("E"), Id("a"), Id("c"))),
                        Equal(D(Id("a"),Id("b")),D(Id("a"),Id("c")))))))),
                "Composing NN once more gives H_a(D(a,b))=D(a,H_a(b)). For equal H images, the two outputs have equal H images. Normality makes H_a act as minus rho on both outputs. Where rho is nonzero it cancels; where rho vanishes, PY makes both outputs zero."),
            Node("raw-real-homogeneity", "raw_real_homogeneity", "Real homogeneity in both slots",
                RawScope(All("a", Elem, All("b", Elem, All("r", Id("Real"),
                    And(Equal(D(Id("a"),Scale(Id("r"),Id("b"))),Scale(Id("r"),D(Id("a"),Id("b")))),
                        Equal(D(Scale(Id("r"),Id("a")),Id("b")),Scale(Id("r"),D(Id("a"),Id("b"))))))))),
                "Original H-fibre constancy gives shears. Six real shears give the determinant-one diagonal action. Applying NN to the scaled first input and inverse-scaled second input gives F_a(r F_a(b))=r H_a(b). One more composition and normality cancel H_a on the two relevant outputs, proving homogeneity. The zero multiplier is treated by PY."),
            Node("raw-scalar-independence", "raw_scalar_independent", "Independence of both central parts",
                RawScope(All("a", Elem, All("b", Elem,
                    Equal(D(Id("a"),Id("b")),D(Call("vectorPart",Id("E"),Id("a")),Call("vectorPart",Id("E"),Id("b"))))))),
                "H_a is independent of the scalar part of its argument. H-fibre constancy and skewness therefore remove the two central parts without assuming additivity of D."),
            Node("raw-k-nested", "raw_K_nested", "The nested original K identity",
                VectorScope(Equal(Call("K",Id("R"),Id("x"),Call("K",Id("R"),Id("x"),Id("y"))),
                    global::StrataLint.Scribe.DefinitionDsl.Subtract(Scale(Dot(Id("x"),Id("y")),Id("x")),Scale(Dot(Id("x"),Id("x")),Id("y"))))),
                "K is defined by restricting the same D to scalar-free original inputs and retaining its three coefficient functions in A. Scalar-zero output identifies the embedded K output with the original D output. The original NN equality then gives the displayed identity."),
            Node("raw-k-geometry", "raw_K_geometry", "Orthogonality and area on the actual coefficient module",
                VectorScope(And(Equal(Dot(Kxy,Id("x")),Num(0)),And(Equal(Dot(Kxy,Id("y")),Num(0)),
                    And(Equal(Dot(Kxy,Kxy),Dot(Call("cross",Id("x"),Id("y")),Call("cross",Id("x"),Id("y")))),
                        All("r",Id("Real"),And(Equal(Call("K",Id("R"),Id("x"),Scale(Id("r"),Id("y"))),Scale(Id("r"),Kxy)),
                            Equal(Call("K",Id("R"),Scale(Id("r"),Id("x")),Id("y")),Scale(Id("r"),Kxy)))))))),
                "Pointwise normality gives the two dot equalities as identities in the actual scalar algebra. The scalar component of PY gives the area equality, using the cross-dot-cross identity over a commutative ring. Real homogeneity of the same original D gives both real homogeneities of K."),
            Node("raw-k-kernel", "raw_K_kernel_translation", "Translation by an original H-kernel vector",
                VectorScope(All("c",Call("Vectors",Id("E")),Imp(Equal(global::StrataLint.Scribe.DefinitionDsl.Subtract(Scale(Dot(Id("x"),Id("c")),Id("x")),Scale(Dot(Id("x"),Id("x")),Id("c"))),Num(0)),
                    Equal(Call("K",Id("R"),Id("x"),global::StrataLint.Scribe.DefinitionDsl.Add(Id("y"),Id("c"))),Kxy)))),
                "The hypothesis is the actual polynomial H_x(c)=0 in A^3. The same original H-fibre theorem gives K(x,y+c)=K(x,y), without additivity of K."))));

    private static Formula Elem => Call("Elem",Id("E"));
    private static Formula Kxy => Call("K",Id("R"),Id("x"),Id("y"));
    private static Formula D(Formula x, Formula y) => Call("D",Id("R"),x,y);
    private static Formula Dot(Formula x, Formula y) => Call("dot",x,y);
    private static Formula Scale(Formula x, Formula y) => Call("smul",x,y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x,FormulaLogicOperator.Implies,y);
    private static Formula RawScope(Formula b) => All("T",Id("TopologicalSpaces"),
        All("E",Call("Original",Id("T")),All("R",Call("Raw",Id("E")),b)));
    private static Formula VectorScope(Formula b) => RawScope(All("x",Call("Vectors",Id("E")),
        All("y",Call("Vectors",Id("E")),b)));
    private static DocumentBlock Node(string id,string declaration,string title,Formula formula,string prose) =>
        Describe.Lean(DescribeId.Create(id),DeclarationHandle.Create("D5/S3/Quantum/Algebra/UnitBridgeRawGeometry."+declaration),
            H(title),StatementSource.FromAuthor(F.Disp(formula)),AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))),DescribeRole.Theorem);
    private static Formula Id(string name) => F.Id(name);
    private static Formula Num(int n) => global::StrataLint.Scribe.DefinitionDsl.Num(n);
    private static Formula Call(string name, params Formula[] args) => global::StrataLint.Scribe.DefinitionDsl.Call(name, args);
    private static Formula Equal(Formula a, Formula b) => global::StrataLint.Scribe.DefinitionDsl.Equal(a,b);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
}
