using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois;

internal sealed class GoldenCubicBlockKummerTowerDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/Galois/GoldenCubicBlockKummerTower.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every cubic-root tower built from the actual Lucas blocks has degree three to the number of stages.",
        H("Lucas-Block Kummer Tower Degree"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-cubic-block-kummer-tower-degree"),
            DeclarationHandle.Create(Prefix + "golden_cubic_block_kummer_tower_degree"),
            H("Every Lucas-block cubic-root tower has degree three to the number of stages"),
            StatementSource.FromAuthor(DegreeFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The base is the third cyclotomic field over the rationals, and the "
                        + "ambient field is its algebraic closure. The block is the natural "
                        + "absolute value of the Lucas expression L at index 3 to the j, "
                        + "squared, plus three; that expression is positive. The roots at "
                        + "positive indices may be any cubic roots of their blocks. The "
                        + "root at index zero is unused.")),
                Paragraph(Text(
                    "The integer noncube and pairwise coprimality results for the actual "
                        + "blocks keep each new block from becoming a cube in the preceding "
                        + "tower. Cubic Galois descent transports a hypothetical cube down "
                        + "one stage, while coprimality prevents cancellation by an earlier "
                        + "block. The cubic polynomial is then irreducible at each stage, "
                        + "and the degrees multiply.")),
                Paragraph(Text(
                    "The statement includes the empty tower at J equal to zero. It gives "
                        + "the degree over the third cyclotomic field for every admissible "
                        + "choice of cubic roots; it does not select positive real roots or "
                        + "assert a discriminant, ramification law, or Galois-group "
                        + "classification."))),
            DescribeRole.Theorem))));

    private static Formula DegreeFormula()
    {
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula rational = Seq(Mathbb, Grp(F.Id("Q")));
        Formula baseField = F.Id("K");
        Formula ambient = F.Id("A");
        Formula block = F.Id("B");
        Formula roots = Beta;
        Formula j = F.Id("j");
        Formula m = F.Id("m");
        Formula J = F.Id("J");
        Formula blockAtJ = new Formula.Subscript(block, j);
        Formula rootAtJ = new Formula.Subscript(roots, j);
        Formula towerZero = Call("tower", roots, D(0));
        Formula towerAtM = Call("tower", roots, m);
        Formula towerNext = Call("tower", roots, Seq(m, Plus, D(1)));
        Formula rootNext = new Formula.Subscript(roots, Seq(m, Plus, D(1)));
        Formula towerAtJ = Call("tower", roots, J);
        Formula lucasIndex = new Formula.Power(D(3), j);
        Formula lucas = new Formula.Subscript(F.Id("L"), lucasIndex);
        Formula degree = Seq(OpenBracket, towerAtJ, Colon, baseField, CloseBracket);

        return Disp(new Formula.Aligned([
            Seq(baseField, Sp, Colon, Eq, Sp, Call("CyclotomicField", D(3), rational),
                Comma, Sp, ambient, Sp, Colon, Eq, Sp, Call("AlgebraicClosure", baseField),
                Comma),
            Seq(blockAtJ, Sp, Colon, Eq, Sp,
                Call("natAbs", Seq(new Formula.Power(lucas, D(2)), Plus, D(3))),
                Comma),
            Seq(towerZero, Sp, Colon, Eq, Sp, baseField, Comma, Sp,
                Forall, Sp, m, Sp, InMacro, Sp, natural, Comma, Sp,
                towerNext, Sp, Colon, Eq, Sp,
                Seq(towerAtM, Open, rootNext, Close), Comma),
            Seq(Forall, Sp, roots, Colon, Sp, natural, Sp, To, Sp, ambient,
                Comma, Sp, Open, Forall, Sp, j, Sp, InMacro, Sp, natural,
                Comma, Sp, D(1), Sp, Le, Sp, j, Sp, Rightarrow, Sp,
                new Formula.Power(rootAtJ, D(3)), Sp, Eq, Sp,
                Call("algebraMap", baseField, ambient, blockAtJ), Close,
                Sp, Rightarrow),
            Seq(Forall, Sp, J, Sp, InMacro, Sp, natural, Comma, Sp,
                degree, Sp, Eq, Sp, new Formula.Power(D(3), J), Dot),
        ]));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
}
