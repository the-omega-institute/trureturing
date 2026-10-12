using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class LengthGramBodyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The common six-length cut body has a Lorentz and upper-half-space coordinate realization.",
        H("One shared body from the actual length Gram matrix"),
        Blocks(
            Paragraph(Text("Let l be six positive real lengths in the order "
                + "(01,02,03,23,13,12). The symmetric matrix G has diagonal entries "
                + "one and off-diagonal entries minus cosh of the corresponding length. "
                + "The set C consists of nonnegative four-coordinate vectors whose "
                + "coordinates sum to one and whose four G-row values are nonpositive. "
                + "Write q(v)=v-transpose G v, r(v)=v/sqrt(-q(v)), and "
                + "b=(1/4,1/4,1/4,1/4). R6 and R4 denote real coordinate spaces. "
                + "B is the Lorentz form with signs (+,+,+,-). The function phi01 "
                + "is the original six-variable cosine formula applied to cosh(l). "
                + "For a future unit timelike y, Psi(y) has horizontal coordinate "
                + "(y0+i*y1)/(y3-y2) and height 1/(y3-y2). H3 denotes the "
                + "repository's HyperbolicThreeSpace with its actual metric topology.")),
            Describe.Lean(
                DescribeId.Create("six-length-shared-radial-body"),
                DeclarationHandle.Create(
                    "D5/S3/Geometry/Hyperideal/LengthGramBody.shared_radial_body"),
                H("Compactness, explicit frame and shared coordinate map"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The barycenter strictly satisfies every cut. "
                        + "A cut equality at a positive coordinate forces that coordinate "
                        + "to exceed one half. If q vanished, every positive coordinate "
                        + "would require a cut equality. Two positive coordinates cannot "
                        + "both exceed one half, while a singleton support violates its "
                        + "own cut. Thus q is strictly negative throughout the same C.")),
                    Paragraph(Text("The positive square-root denominator makes r "
                        + "continuous. The sum of the image coordinates recovers its "
                        + "reciprocal scale, so r is injective. Its image is compact "
                        + "and nonempty, and the quadratic value there equals minus one.")),
                    Paragraph(Text("The strict condition on phi01 makes the final "
                        + "square root in the explicit four-vector frame positive. "
                        + "The frame's Lorentz Gram is exactly G and its determinant "
                        + "is positive. Congruence with diag(1,1,1,-1) gives det(G)<0. "
                        + "Every point of the same radial body is future unit timelike. "
                        + "Its positive denominator y3-y2 defines Psi throughout C. "
                        + "The coordinate inverse proves injectivity, and the existing "
                        + "coordinate homeomorphism proves continuity into actual H3.")),
                    Paragraph(Text("This closes the shared compact coordinate-body "
                        + "and frame step of the original six-length construction. "
                        + "It does not yet assert three-dimensional interior, complete "
                        + "triangular/hexagonal incidence, geodesic intervals, prescribed "
                        + "edge distances, dihedral angles or relabeling isometries. "
                        + "Those obligations retain the original all-six strict source "
                        + "cosine domain; one strict condition suffices for this frame step.")),
                    Paragraph(Text("For the original volume calculation, retain all six positive lengths and all "
                        + "six strict source cosines, and fix any original witnesses M and f satisfying the "
                        + "displayed frame and radial-coordinate equations. Use EuclideanSpace Real (Fin 3) "
                        + "with its L2 norm and canonical three-dimensional Haar volume. Set "
                        + "A(u)=(1-u0-u1-u2,u0,u1,u2), D=A inverse-image C, X=A(u) times M, "
                        + "s=sqrt(-q(A(u))) and d=X3-X2. The sum-one condition on C proves A(D)=C: "
                        + "the inverse chart is P(v)=(v1,v2,v3). The same future unit timelike "
                        + "radial vector is Y=X/s, so s>0 and d=s*(Y3-Y2)>0 on all of D. "
                        + "Consequently the actual coordinates of f(A(u)) are (F0+i*F1,F2), where "
                        + "F(u)=(X0/d,X1/d,s/d). This identifies the literal original map, including "
                        + "all cut-boundary points; no alternate frame or body is selected.")),
                    Paragraph(Text("The Frechet derivative rules give the ambient derivative of this F "
                        + "where q(A(u))<0 and d is nonzero. For h in Real3, put "
                        + "v=(-h0-h1-h2,h0,h1,h2), w=v times M and delta=w3-w2. "
                        + "Then Ds[h]=-B(X,w)/s, and the derivative is "
                        + "DF[h]=(w0/d-X0*delta/d^2, w1/d-X1*delta/d^2, "
                        + "-B(X,w)/(s*d)-s*delta/d^2). This is an actual derivative of the "
                        + "coordinate function. Its restriction supplies a derivative within D "
                        + "even where a cut equality is active; boundary smoothness is unnecessary.")),
                    Paragraph(Text("The signed determinant follows by homogeneous coordinates. "
                        + "Let H(X)=(X0,X1,s,X3-X2). Its four-dimensional derivative has determinant d/s "
                        + "and sends X to H(X). The matrix with rows A and the three coordinate derivatives "
                        + "of A has determinant one, so the matrix with rows X and the three derivatives "
                        + "of X has determinant det(M). Applying DH gives a determinant det(M)*d/s. "
                        + "Subtract delta/d times the first row from each derivative row. The last "
                        + "column becomes (d,0,0,0), while each remaining derivative row is d times "
                        + "the corresponding derivative row of F. Expansion in the last column gives "
                        + "-d^4*det(DF). Thus det(DF)=-det(M)/(s*d^3), with the sign fixed by "
                        + "row-vector action and output order (horizontal real, horizontal imaginary, height).")),
                    FormulaBlock(Eq(Call("det", Call("DF", F.Id("u"))),
                        new Formula.Fraction(F.Seq(F.Minus, Call("det", F.Id("M"))),
                            Mul(F.Id("s"), new Formula.Power(F.Id("d"), F.D(3)))))),
                    Paragraph(Text("The same frame congruence G=M*diag(1,1,1,-1)*transpose(M) gives "
                        + "det(G)=-det(M)^2 and sqrt(-det(G))=abs(det(M)). Since F2=s/d and s,d are "
                        + "positive, cancellation yields the exact weighted Jacobian below. The "
                        + "three-dimensional determinant uses the standard L2 orthonormal coordinates; "
                        + "there is no induced four-dimensional simplex measure or extra hyperplane factor.")),
                    FormulaBlock(Eq(Mul(new Formula.Power(new Formula.Subscript(F.Id("F"), F.D(2)), F.Seq(F.Minus,F.D(3))),
                            Call("abs", Call("det", Call("DF", F.Id("u"))))),
                        new Formula.Fraction(Call("sqrt", F.Seq(F.Minus,Call("det", F.Id("G")))),
                            new Formula.Power(new Formula.Binary(F.D(0),FormulaBinaryOperator.Subtract,
                                Call("q", Call("A", F.Id("u")))), F.D(2))))),
                    Paragraph(Text("Let N take the native coordinates of a point in H3 to the real triple "
                        + "(horizontal real, horizontal imaginary, height). Then F(D)=N(range(f)) "
                        + "for the same f. Packing a real triple back into (Complex,Real) is injective; "
                        + "the original injectivity of f and the inverse affine chart therefore give "
                        + "injectivity of F on D. The projection P sends the compact C onto D, so D "
                        + "is compact and measurable. The original coordinate homeomorphism makes N "
                        + "continuous, and N(range(f)) is compact and measurable in Real3. Thus the "
                        + "image correspondence and the domain conditions needed by measurable-set "
                        + "change of variables apply to the original body including its entire boundary.")),
                    Paragraph(Text("These identities give the actual change-of-variables Jacobian with the original "
                        + "frame equations. To identify the "
                        + "normalized native Hausdorff mass of the same range(f), the remaining step is "
                        + "measurable-set change of variables on the actual image, followed by "
                        + "HyperbolicNormalizedDensity.raw_native_density and its existing exact L2 "
                        + "orthonormal-cube Haar calibration. Native mass equality, positive finite native "
                        + "mass and witness independence are not conclusions of the Jacobian calculation "
                        + "alone. The flat-boundary limit, face and angle identification, Schlaefli variation "
                        + "and co-volume conclusions remain separate; zero lengths are excluded."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var l = F.Id("l");
        var v = F.Id("v");
        var c = Call("C", l);
        var r = Call("r", l);
        var image = Call("image", r, c);
        return All("l", F.Id("R6"), Implies(
            All("k", Call("Fin", F.D(6)), Lt(F.D(0), Call("l", F.Id("k")))),
            And(Call("IsCompact", c), In(F.Id("b"), c),
                All("i", Call("Fin", F.D(4)), Lt(Call("Gb", l, F.Id("i")), F.D(0))),
                All("v", F.Id("R4"), Implies(In(v, c), Lt(Call("q", l, v), F.D(0)))),
                Call("ContinuousOn", r, c), Call("InjOn", r, c),
                Call("IsCompact", image), Call("Nonempty", image),
                All("v", F.Id("R4"), Implies(In(v, c),
                    Eq(Call("q", l, Call("r", l, v)), F.Seq(F.Minus, F.D(1))))),
                PhysicalBody(l, c))));
    }

    private static Formula PhysicalBody(Formula l, Formula c)
    {
        var m = F.Id("m");
        var f = F.Id("f");
        var v = F.Id("v");
        var y = F.Id("y");
        var phi = Call("phi01", l);
        var minusOne = F.Seq(F.Minus, F.D(1));
        return Implies(And(Lt(minusOne, phi), Lt(phi, F.D(1))),
            Exists("m", F.Id("Matrix4"), And(
                All("i", Call("Fin", F.D(4)),
                    All("j", Call("Fin", F.D(4)),
                        Eq(Call("B", Call("row", m, F.Id("i")), Call("row", m, F.Id("j"))),
                            Call("G", l, F.Id("i"), F.Id("j"))))),
                Lt(F.D(0), Call("det", m)), Lt(Call("det", Call("G", l)), F.D(0)),
                Exists("f", Call("Maps", c, F.Id("H3")), And(
                    Call("Continuous", f), Call("Injective", f),
                    Call("IsCompact", Call("range", f)), Call("Nonempty", Call("range", f)),
                    All("v", c, Exists("y", F.Id("R4"), And(
                        Eq(y, Call("vecMul", Call("r", l, v), m)),
                        Eq(Call("B", y, y), minusOne), Lt(F.D(0), Call("coord", y, F.D(3))),
                        Eq(Call("coordinates", Call("f", v)), Call("Psi", y))))))))));
    }

    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);

    private static DocumentBlock FormulaBlock(Formula p) => new DocumentBlock.DisplayFormula(p);

    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists,
            FormulaIdentifier.Create(name), domain, body);

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(name), domain, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula And(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula In(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
}
