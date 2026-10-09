using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class KaselDisplacementLadderLowerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every valid normalized Kasel scheme has distinguished displacement at least m minus two.",
        H("The Kasel Displacement Lower Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("kasel-displacement-lower-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Permutation/KaselDisplacementLadderLower.lower_bound"),
                H("A distinguished value attains the lower bound"),
                StatementSource.FromAuthor(LowerBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural m at least two and every pair of natural-valued "
                    + "functions s and r forming a valid normalized scheme on SA m, some "
                    + "distinguished value v has stage at least its block index divided by "
                    + "two plus m minus two. At m equal to two, take v equal to three and "
                    + "apply normalization. For m at least three, suppose both fifteen and "
                    + "sixteen have stage below m. Put M equal to twice four to the power "
                    + "m minus one. Every value in (M, 2M] has block index 2m and hence "
                    + "stage at least m. Counting predecessors in the strict total "
                    + "concatenation order gives an injective natural-valued rank that "
                    + "preserves and reflects that order. Validity excludes both monotone "
                    + "arithmetic progressions in this block. Each attack from fifteen or "
                    + "sixteen forces its guard before its bottom, since the attack "
                    + "itself precedes the bottom and validity forbids a monotone "
                    + "progression. These ranks form an Erdos-Graham order gadget at "
                    + "scale M at least thirty-two. The frozen all-scale impossibility "
                    + "theorem gives a contradiction. Thus fifteen or sixteen has stage "
                    + "at least m, which is exactly the required lower bound."))),
                DescribeRole.Theorem)),
        []));

    private static Formula LowerBoundFormula()
    {
        Formula m = F.Id("m"), s = F.Id("s"), r = F.Id("r"), v = F.Id("v");
        Formula horizon = Call("SA", m);
        Formula premises = Seq(
            Open, Call("Valid", horizon, s, r), Sp, Land, Sp,
            Call("Normalized", horizon, s), Close);
        Formula halfBlock = new Formula.Floor(new Formula.Fraction(Call("block", v), D(2)));
        Formula displacement = new Formula.Binary(
            m, FormulaBinaryOperator.Subtract, D(2));
        Formula lower = new Formula.Binary(
            halfBlock, FormulaBinaryOperator.Add, displacement);
        Formula bound = Seq(lower, Sp, Le, Sp, Call("s", v));
        Formula witness = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("v"),
            F.Id("distinguished"),
            bound);
        Formula schemes = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", Functions()), Bound("r", Functions())],
            Implies(premises, witness));
        return Disp(new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("m"),
            Naturals(),
            Implies(Seq(D(2), Sp, Le, Sp, m), schemes)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Functions() =>
        new Formula.TypeArrow(Naturals(), Naturals());

    private static Formula Naturals() => Seq(Mathbb, Sp, Grp(F.Id("N")));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);
}
