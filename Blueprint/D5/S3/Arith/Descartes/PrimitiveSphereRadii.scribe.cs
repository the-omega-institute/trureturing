using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Descartes;

internal sealed class PrimitiveSphereRadiiDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The 3-adic orders of primitive spherical Descartes radii.",
        H("The 3-adic clause of A390148"),
        Blocks(Describe.Lean(
            DescribeId.Create("primitive-sphere-radii-three-adic"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Descartes/PrimitiveSphereRadii.primitive_sphere_radii_v3"),
            H("One zero order and three equal positive orders"),
            StatementSource.FromAuthor(MainFormula()),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/ArithUnits/hohn2025a390148")),
            Blocks(
                Paragraph(Text(
                    "The index i ranges over four coordinates. The radii are positive natural "
                    + "numbers, and gcd means their common gcd, without pairwise coprimality. "
                    + "The reciprocal equation is interpreted over the rationals. The function "
                    + "v with subscript 3 is the natural 3-adic valuation. No ordering is assumed.")),
                Paragraph(Text(
                    "Let L be the least common multiple of the radii and put b(i)=L/r(i). "
                    + "These are positive integers with common gcd one. Indeed, if d divides "
                    + "every b(i), then every radius divides L/d. Minimality of L forces d=1. "
                    + "Multiplying the reciprocal equation by L squared gives the same "
                    + "coefficient-three equation for the integer curvatures b.")),
                Paragraph(Text(
                    "The equation first makes the sum of b divisible by three, and then "
                    + "makes the sum of its squares divisible by three. A nonzero residue "
                    + "modulo three has square one. Consequently the number of unit "
                    + "coordinates is a positive multiple of three at most four, hence three.")),
                Paragraph(Text(
                    "The product b(i)r(i)=L gives v3(b(i))+v3(r(i))=v3(L). Thus the three "
                    + "unit curvatures correspond to three radii of the largest order e. "
                    + "Order e cannot be zero, since that would give four such radii. "
                    + "Primitivity supplies a radius of order zero, which occupies the "
                    + "single remaining coordinate. The OEIS entry states this clause "
                    + "as a conjecture; its other prime conditions, repetition formula "
                    + "and chain conjecture are separate."))),
            DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Square(Formula value) => new Formula.Power(value, D(2));
    private static Formula Ri() => Seq(V("r"), Underscore, V("i"));
    private static Formula Val() => Seq(V("v"), Underscore, D(3), Par(Ri()));
    private static Formula SumI(Formula value) => Seq(Sum, Underscore, V("i"), value);

    private static Formula MainFormula()
    {
        var reciprocal = Seq(Frac, Grp(D(1)), Grp(Ri()));
        var equation = Seq(Square(Par(SumI(reciprocal))), Eq,
            D(3), SumI(Square(Par(reciprocal))));
        var fiber = Seq(OpenBrace, V("i"), Colon, Val(), Eq, V("e"), CloseBrace);
        var conclusion = Seq(Exists, Sp, V("e"), InMacro, Mathbb, Grp(V("N")), Comma,
            D(0), Lt, V("e"), Sp, Land, Sp,
            Lvert, fiber, Rvert, Eq, D(3), Sp, Land, Sp,
            Forall, Sp, V("i"), Comma, Par(Seq(Val(), Eq, D(0), Sp, Lor, Sp, Val(), Eq, V("e"))));
        return Disp(Seq(Forall, Sp, V("r"), Colon, Operatorname, Grp(V("Fin")), Par(D(4)),
            To, Mathbb, Grp(V("N")), Comma,
            Par(Seq(Par(Seq(Forall, Sp, V("i"), Comma, D(0), Lt, Ri())), Sp, Land, Sp,
                Gcd, Par(V("r")), Eq, D(1), Sp, Land, Sp, equation)),
            Sp, Implies, Sp, conclusion));
    }
}
