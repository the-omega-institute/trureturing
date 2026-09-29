using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois;

internal sealed class GoldenCubicBlockPositiveRootTowerDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/Galois/GoldenCubicBlockPositiveRootTower.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The positive real Lucas-block cube roots generate a degree-three tower over the concrete cubic cyclotomic field in the complex numbers.",
        H("Positive-Root Lucas-Block Tower"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-cubic-block-positive-root-tower-degree"),
            DeclarationHandle.Create(Prefix + "golden_cubic_block_positive_root_tower_degree"),
            H("The concrete positive-root tower has degree three to the number of blocks"),
            StatementSource.FromAuthor(DegreeFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Here omega is exp(2 pi i / 3), and K is the concrete subfield "
                        + "Q(omega) of C. Each B_j is the positive integer "
                        + "L_(3^j)^2 + 3. The element beta_j is its positive real cube "
                        + "root, embedded in C; K_J adjoins precisely those beta_j with "
                        + "indices from one through J.")),
                Paragraph(Text(
                    "The proof transports the degree from the abstract third cyclotomic "
                        + "field to this complex copy. In a field containing the cubic roots "
                        + "of unity, any two cube roots of the same nonzero block generate "
                        + "the same subfield. This identifies each positive-root stage with "
                        + "the corresponding abstract stage, whose degree is three.")),
                Paragraph(Text(
                    "For positive J this is the Lucas-block tower of the stated theory. "
                        + "The Lean conclusion also includes J equal to zero, where the "
                        + "tower is K and has degree one. No field discriminant, "
                        + "ramification law, or Galois-group structure is asserted."))),
            DescribeRole.Theorem))));

    private static Formula DegreeFormula()
    {
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula rational = Seq(Mathbb, Grp(F.Id("Q")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula omega = Omega;
        Formula field = F.Id("K");
        Formula j = F.Id("j");
        Formula J = F.Id("J");
        Formula blockAtJ = new Formula.Subscript(F.Id("B"), j);
        Formula rootAtJ = new Formula.Subscript(Beta, j);
        Formula towerAtJ = new Formula.Subscript(field, J);
        Formula lucas = new Formula.Subscript(F.Id("L"), new Formula.Power(D(3), j));
        Formula positiveReals = new Formula.Subscript(real, Seq(Gt, D(0)));
        Formula rootIndices = Seq(OpenBrace, rootAtJ, Sp, Mid, Sp,
            j, Sp, InMacro, Sp, natural, Comma, Sp,
            D(1), Sp, Le, Sp, j, Sp, Le, Sp, J, CloseBrace);
        Formula degree = Seq(OpenBracket, towerAtJ, Colon, field, CloseBracket);

        return Disp(new Formula.Aligned([
            Seq(omega, Sp, Colon, Eq, Sp,
                Call("exp", Seq(Frac,
                    Grp(D(2), Sp, Pi, Sp, F.Id("i")), Grp(D(3)))), Comma, Sp,
                field, Sp, Colon, Eq, Sp, Seq(rational, Open, omega, Close),
                Sp, Subset, Sp, complex, Comma),
            Seq(blockAtJ, Sp, Colon, Eq, Sp,
                Seq(new Formula.Power(lucas, D(2)), Plus, D(3)), Comma, Sp,
                rootAtJ, Sp, Colon, Eq, Sp,
                new Formula.Power(blockAtJ, Seq(Frac, Grp(D(1)), Grp(D(3)))),
                Sp, InMacro, Sp, positiveReals, Sp, Subset, Sp, complex, Comma),
            Seq(towerAtJ, Sp, Colon, Eq, Sp,
                Call("adjoin", field, rootIndices), Comma),
            Seq(Forall, Sp, J, Sp, InMacro, Sp, natural, Comma, Sp,
                degree, Sp, Eq, Sp, new Formula.Power(D(3), J), Dot),
        ]));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
}
