using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class LowDimensionalBorsukUlamDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Topology/LowDimensionalBorsukUlam.";

    private static LibraryNoteRef Borsuk => LibraryNoteRef.Create("D5/L/Topology/borsuk1933spheres");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A map from the unit sphere of R^(d+1) to R^d that is continuous on the sphere takes equal values at some pair of antipodal points when d <= 2; consequently, for d <= 2 and d < m, no map from R^m to R^d is continuous and injective on a nonempty open set.",
        H("The Borsuk-Ulam theorem in dimensions at most two"),
        Blocks(
            Node("exists-eq-neg-of-le-two", "exists_eq_neg_of_le_two",
                "Antipodal coincidence in dimensions at most two",
                StatementSource.FromAuthor(AntipodalFormula()), AssessedProvenance.FromLiterature(Borsuk),
                "Let d <= 2 and let f be a map from Euclidean space of dimension d + 1 to Euclidean space of dimension d that is continuous on the unit sphere. "
                    + "Then f x = f (-x) for some point x of the unit sphere. "
                    + "This is Borsuk's Satz II, the classical Borsuk-Ulam theorem, in the cases d <= 2 (Satz II for the d-dimensional sphere); the theorem for general d is not stated here, and it is not available in the underlying formal library. "
                    + "For d = 0 the target is a single point. "
                    + "For d = 1 the function g x = f x - f (-x) with values in the real line is continuous on the unit circle and odd, g (-x) = -g x, so it takes a value of each sign at the antipodal points of a fixed point; since the circle is connected, the intermediate value theorem gives a zero of g. "
                    + "For d = 2 the plane is identified isometrically with the complex numbers, and the map x -> f x - f (-x) becomes a continuous odd complex-valued map on the unit sphere of three-space; such a map has a zero, which is the required point.",
                DescribeRole.Theorem),
            Node("not-inj-on-of-lt", "not_injOn_of_lt",
                "No continuous injection of an open set into a lower dimension at most two",
                StatementSource.FromAuthor(InjectionFormula()), AssessedProvenance.FromRepo(),
                "Let d <= 2 and d < m, let U be a nonempty open subset of Euclidean space of dimension m, and let f be a map from Euclidean space of dimension m to Euclidean space of dimension d that is continuous on U. "
                    + "Then f is not injective on U. "
                    + "This is the classical consequence of invariance of domain that a nonempty open subset of Euclidean space of dimension m admits no continuous injection into Euclidean space of dimension d < m, here only for d <= 2; invariance of domain itself, the openness of the image of a continuous injection between open subsets of the same Euclidean space, is not stated. "
                    + "Choose a point p of U and a radius r with the ball of radius r about p contained in U. "
                    + "Write m = d + 1 + k and embed Euclidean space of dimension d + 1 isometrically as the first d + 1 coordinates; scaling the unit sphere of dimension d by a positive factor t smaller than r and translating it to p gives a sphere y -> p + t y inside U. "
                    + "The composition of f with this map is continuous on the unit sphere of dimension d, so it takes equal values at some antipodal pair x and -x. "
                    + "Injectivity of f on U would give p + t x = p - t x, hence x = 0, which is not a point of the unit sphere.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement,
        AssessedProvenance provenance, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("low-dimensional-borsuk-ulam-" + id),
            DeclarationHandle.Create(Prefix + selector), H(title), statement, provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Ap(Formula function, Formula argument) => new Formula.Apply(function, [argument]);
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Euclid(Formula n) => Call("EuclideanSpace", Reals, Call("Fin", n));
    private static Formula Sphere => Call("sphere", D(0), D(1));

    private static Formula AntipodalFormula()
    {
        Formula d = F.Id("d"), f = F.Id("f"), x = F.Id("x");
        Formula succ = Seq(d, Sp, Plus, Sp, D(1));
        return Disp(Seq(
            Forall, Sp, d, Colon, Sp, Naturals, Comma, Sp, d, Sp, Leq, Sp, D(2), Sp, Rightarrow, Sp,
            Forall, Sp, f, Colon, Sp, Euclid(succ), Sp, To, Sp, Euclid(d), Comma, Sp,
            Call("ContinuousOn", f, Sphere), Sp, Rightarrow, Sp,
            Exists, Sp, x, Sp, InMacro, Sp, Sphere, Comma, Sp,
            Ap(f, x), Sp, Eq, Sp, Ap(f, Seq(Minus, x))));
    }

    private static Formula InjectionFormula()
    {
        Formula m = F.Id("m"), d = F.Id("d"), u = F.Id("U"), f = F.Id("f");
        return Disp(Seq(
            Forall, Sp, m, Comma, Sp, d, Colon, Sp, Naturals, Comma, Sp,
            d, Sp, Leq, Sp, D(2), Sp, Rightarrow, Sp, d, Sp, Lt, Sp, m, Sp, Rightarrow, Sp,
            Forall, Sp, u, Colon, Sp, Call("Set", Euclid(m)), Comma, Sp,
            Call("IsOpen", u), Sp, Rightarrow, Sp, Call("Nonempty", u), Sp, Rightarrow, Sp,
            Forall, Sp, f, Colon, Sp, Euclid(m), Sp, To, Sp, Euclid(d), Comma, Sp,
            Call("ContinuousOn", f, u), Sp, Rightarrow, Sp,
            Neg, Sp, Call("InjOn", f, u)));
    }
}
