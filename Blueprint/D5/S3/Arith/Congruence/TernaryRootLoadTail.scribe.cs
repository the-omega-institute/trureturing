using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class TernaryRootLoadTailDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite sequence of ternary-root choices has a uniform discounted load-square bound.",
        H("Ternary Root Load Tails"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-root-itinerary-bound"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Congruence/TernaryRootLoadTail.root_load_tail_le"),
            H("An explicit bound for every finite itinerary"),
            StatementSource.FromAuthor(BoundFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The nonnegative real numbers d0 and d1 bound the available densities "
                    + "in two ternary roots. Natural numbers a and b count earlier positive "
                    + "test depths assigned to each root. A finite Boolean list records all "
                    + "remaining choices, with false selecting the first root.")),
                Paragraph(Text(
                    "The function rootLoadTail is zero on an empty list. A false step adds "
                    + "(3 + 2a)d0, increases a by one, and divides the remaining cost by three; "
                    + "a true step adds (3 + 2b)d1 and similarly increases b. The coefficient "
                    + "three accounts for a diagonal term and two intersections with the "
                    + "constant test class. Previous tests in the same root contribute two each.")),
                Paragraph(Text(
                    "The bound holds for every finite length and every pair of initial counts. "
                    + "Induction on the itinerary preserves the explicit maximum of the two "
                    + "root potentials. In a ternary congruence calculation, initial counts "
                    + "a = 1 and b = 0 and the depth-two factor 1/9 give a remaining-cost bound "
                    + "max(d0, 2d1/3). Relating an actual residue layout to these choices and "
                    + "bounding its other prime coordinates require additional arguments."))),
            DescribeRole.Theorem))));

    private static Formula BoundFormula()
    {
        Formula d0 = F.Id("d0");
        Formula d1 = F.Id("d1");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula itinerary = F.Id("w");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula hypothesis = new Formula.Logic(
            Le(D(0), d0), FormulaLogicOperator.And, Le(D(0), d1));
        Formula conclusion = Le(
            Call("rootLoadTail", d0, d1, a, b, itinerary),
            Mul(D(3), Call("max", Mul(d0, Add(a, D(2))), Mul(d1, Add(b, D(2))))));
        return Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("d0", real), Bound("d1", real), Bound("a", natural),
             Bound("b", natural), Bound("w", Call("List", F.Id("Bool")))],
            new Formula.Logic(hypothesis, FormulaLogicOperator.Implies, conclusion)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
