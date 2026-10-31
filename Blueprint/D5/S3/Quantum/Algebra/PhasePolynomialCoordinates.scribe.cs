using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class PhasePolynomialCoordinatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cartesian and conjugate-coordinate polynomials are uniquely equivalent and preserve degree.", H("Faithful Complex Polynomial Coordinates"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-cartesian"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/PhasePolynomialCoordinates.actual_cartesian"),
                H("Actual evaluation"), StatementSource.FromAuthor(Disp(Coordinates(All("p", P, All("z", V, Rel(Call("eval", Call("cartesian", F.Id("z")), Call("toCartesian", F.Id("p"))), Eq, Actual(F.Id("p"), F.Id("z"))))), false))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Poly(iota) is the polynomial algebra over the complex numbers on iota plus a second copy of iota. Coefficients and finite supports are unrestricted. The first copy represents z and the second its conjugate. Cartesian substitution sends these variables to x+iy and x-iy. Actual evaluation sets the second copy to the complex conjugate of the first. For every vector, Cartesian evaluation after substitution equals actual evaluation."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-injective"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/PhasePolynomialCoordinates.actual_injective"),
                H("Faithfulness on the actual conjugate diagonal"), StatementSource.FromAuthor(Disp(Coordinates(Call("Injective", Call("actual", F.Id("iota"))), false))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two paired-variable polynomials agreeing at every actual complex vector are equal. This follows by the invertible Cartesian substitution and polynomial extensionality on a product of infinite real axes. No injectivity on the conjugate diagonal is assumed. The coordinate type may be empty and need not be finite for this statement."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cartesian-totalDegree"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/PhasePolynomialCoordinates.cartesian_totalDegree"),
                H("Total degree correspondence"), StatementSource.FromAuthor(Disp(Coordinates(All("p", P, Rel(Call("totalDegree", Call("toCartesian", F.Id("p"))), Eq, Call("totalDegree", F.Id("p")))), false))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both inverse substitutions are linear homogeneous substitutions. Each weakly decreases total degree, so invertibility gives equality. The natural total-degree convention includes degree zero for the zero polynomial. Constants and arbitrary degrees remain in scope."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("real-coordinates-unique"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/PhasePolynomialCoordinates.real_coordinates_unique"),
                H("Unique expansion of real-coordinate polynomials"), StatementSource.FromAuthor(Disp(Coordinates(All("q", P, Unique("p", P, All("z", V, Rel(Actual(F.Id("p"), F.Id("z")), Eq, Call("eval", Call("cartesian", F.Id("z")), F.Id("q")))))), false))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every polynomial in the real and imaginary coordinates has exactly one expansion in z and its conjugate with the same actual values. Complex coefficients permit all complex-valued polynomial functions on the underlying real coordinate space; real coefficients are included through their canonical embedding. The inverse substitution is x=(z+w)/2 and y=(z-w)/(2i)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cartesian-homogeneous"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/PhasePolynomialCoordinates.cartesian_homogeneous"),
                H("Homogeneous degree correspondence"), StatementSource.FromAuthor(Disp(Coordinates(All("p", P, All("n", F.Id("N"), Rel(Call("IsHomogeneous", Call("toCartesian", F.Id("p")), F.Id("n")), Iff, Call("IsHomogeneous", F.Id("p"), F.Id("n"))))), false))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural n, the polynomial is homogeneous of degree n exactly when its Cartesian image is. This uses the homogeneous substitution theorem in both directions. The zero polynomial is homogeneous of every degree, and no nonzero hypothesis is imposed."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) { content.Add(Comma); content.Add(Sp); }
            content.Add(arguments[i]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Unique(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Star, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Rel(Formula left, Formula relation, Formula right) =>
        Seq(Open, left, Sp, relation, Sp, right, Close);
    private static Formula And(params Formula[] parts)
    {
        var content = new List<Formula> { Open };
        for (var i = 0; i < parts.Length; i++)
        {
            if (i > 0) { content.Add(Sp); content.Add(Land); content.Add(Sp); }
            content.Add(parts[i]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }
    private static Formula Coordinates(Formula body, bool finite = true) =>
        All("iota", F.Id("Type"), finite
            ? Seq(OpenBracket, Call("Fintype", F.Id("iota")), CloseBracket, Sp, body) : body);
    private static Formula P => Call("Poly", F.Id("iota"));
    private static Formula V => Rel(F.Id("iota"), To, F.Id("C"));
    private static Formula M => Call("Matrix", F.Id("iota"), F.Id("iota"), F.Id("C"));
    private static Formula Actual(Formula p, Formula z) => Call("actual", p, z);
    private static Formula Q(Formula h, Formula z) => Call("starDotMul", h, z);
}
