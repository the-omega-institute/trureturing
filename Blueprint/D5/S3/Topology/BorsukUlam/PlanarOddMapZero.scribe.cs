using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.BorsukUlam;

internal sealed class PlanarOddMapZeroDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A continuous odd complex-valued map on the unit sphere in real three-space has a zero.",
        H("The planar odd-map zero theorem"),
        Blocks(Describe.Lean(
            DescribeId.Create("planar-odd-map-zero"),
            DeclarationHandle.Create("D5/S3/Topology/BorsukUlam/PlanarOddMapZero.planar_odd_map_zero"),
            H("A zero of an odd map on the two-sphere"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Topology/borsuk1933spheres")),
            Blocks(
                Paragraph(Text(
                    "This is Borsuk's Satz II (1933) for n=2 applied to an odd map, identifying the target plane with the complex numbers, proved here from the covering-space lift. "
                        + "The function f is defined on the whole ambient Euclidean space, but continuity and oddness are required only on its unit sphere. "
                        + "No restriction on f away from the sphere is used.")),
                Paragraph(Text(
                    "Suppose f has no zero on the sphere. Let D be the closed unit disk in the complex plane. "
                        + "It is a nonempty convex set, hence contractible and locally path connected. "
                        + "Send a disk point z to the upper half of the sphere by the vector with coordinates Re(z), Im(z) and the nonnegative square root of 1−‖z‖². "
                        + "The disk inequality makes the square root's argument nonnegative, and the sum of the coordinate squares is one. "
                        + "This map is continuous, and on the boundary its values at −z and z are negatives of one another.")),
                Paragraph(Text(
                    "Compose f with this map to the sphere to obtain a continuous nonvanishing complex function q on D. "
                        + "Normalize it by q(z) divided by Complex.ofReal(‖q(z)‖), obtaining a continuous circle-valued map g. "
                        + "Choose a real argument for g at the disk's center. The covering map Circle.exp then lifts g to a continuous real-valued map F on the contractible disk, with that chosen central value. "
                        + "On the boundary circle write l(z) = F(z), using the boundary inclusion into D. Then l is continuous and Circle.exp(l(z)) = g(z).")),
                Paragraph(Text(
                    "Oddness of f and the antipodal identity on the boundary give g(−z) = −g(z). "
                        + "Thus the continuous real function delta(z) = l(−z)−l(z) has exponential constantly equal to minus one. "
                        + "A continuous map from the connected circle into a single fiber of this covering is constant, so delta(−1) = delta(1). "
                        + "The definition also gives delta(−1) = −delta(1), forcing delta(1) = 0. "
                        + "Its exponential is therefore one as well as minus one, a contradiction. Hence f vanishes at some point of the unit sphere."))),
            DescribeRole.Theorem))));

    private static Formula Statement() => All("f", Arrow(EuclideanType(), Complexes()),
        Imp(At(Qualified("ContinuousOn"), X("f"), Sphere()),
            Imp(All("v", EuclideanType(), Imp(Member(X("v"), Sphere()),
                Equal(At(X("f"), Negative(X("v"))), Negative(At(X("f"), X("v")))))),
                Some("v", EuclideanType(), And(Member(X("v"), Sphere()),
                    Equal(At(X("f"), X("v")), Typed(D(0), Complexes())))))));
    private static Formula Sphere() => At(Qualified("Metric", "sphere"), Typed(D(0), EuclideanType()), Typed(D(1), Reals()));
    private static Formula EuclideanType() => At(Qualified("EuclideanSpace"), Reals(), At(Qualified("Fin"), D(3)));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Arrow(Formula left, Formula right) => new Formula.TypeArrow(Parenthesized(left), Parenthesized(right));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Negative(Formula value) => new Formula.Negate(Parenthesized(value));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
}
