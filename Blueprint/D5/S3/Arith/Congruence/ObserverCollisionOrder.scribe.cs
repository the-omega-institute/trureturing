using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class ObserverCollisionOrderDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Arith/Congruence/ObserverCollisionOrder."
            + "observer_collision_order_eq_padic_valuation_and_exists";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Observer collision order is the p-adic valuation, with a positive nontrivial witness.",
        H("Observer Collision Order"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("observer-collision-order-is-p-adic-valuation"),
                DeclarationHandle.Create(Declaration),
                H("Collision order is the p-adic valuation and is realizable"),
                StatementSource.FromAuthor(CollisionOrderFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a prime p, suppose two integer readings agree modulo p^r but "
                            + "disagree modulo p^(r + 1). Their difference is then divisible "
                            + "by p^r and not by p^(r + 1), so its p-adic valuation is r.")),
                    Paragraph(Text(
                        "The proof imports the stronger precision-reading equivalence, which "
                            + "characterizes agreement at every precision by an inequality "
                            + "against padicValInt. It introduces no parallel collision-order "
                            + "or valuation definition.")),
                    Paragraph(Text(
                        "The explicit readings a = 0 and b = 4 at p = 2 agree at order two "
                            + "and disagree at order three. This realizes the definition at "
                            + "the positive nontrivial order r = 2.")),
                    Paragraph(Text(
                        "The source atom's separate golden-ramification sentence is not included: "
                            + "the atom supplies no self-contained number-field hypotheses from "
                            + "which that statement could be formalized."))),
                DescribeRole.Theorem))));

    private static Formula Reading(Formula prime, Formula order, Formula value) =>
        Call("precisionReading", prime, order, value);

    private static Formula CollisionConditions(
        Formula prime,
        Formula order,
        Formula left,
        Formula right) =>
        Seq(
            Call("Prime", prime), Sp, Land, Sp,
            Reading(prime, order, left), Sp, Eq, Sp, Reading(prime, order, right),
            Sp, Land, Sp,
            Reading(prime, Seq(order, Sp, Plus, Sp, D(1)), left), Sp, Neq, Sp,
            Reading(prime, Seq(order, Sp, Plus, Sp, D(1)), right));

    private static Formula Valuation(
        Formula prime,
        Formula left,
        Formula right) =>
        Call("padicValInt", prime, Seq(left, Sp, Minus, Sp, right));

    private static Formula CollisionOrderFormula()
    {
        Formula prime = F.Id("p");
        Formula order = F.Id("r");
        Formula left = F.Id("a");
        Formula right = F.Id("b");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        Formula general = Seq(
            Forall, Sp, prime, Comma, Sp, order, Sp, InMacro, Sp, naturals, Comma,
            RowBreak, Grp(),
            left, Comma, Sp, right, Sp, InMacro, Sp, integers, Comma,
            RowBreak, Grp(),
            CollisionConditions(prime, order, left, right), Sp, Rightarrow, Sp,
            Valuation(prime, left, right), Sp, Eq, Sp, order);

        Formula witnessPrime = D(2);
        Formula witnessOrder = D(2);
        Formula witnessLeft = D(0);
        Formula witnessRight = D(4);
        Formula witness = Seq(
            Exists, Sp, prime, Comma, Sp, order, Sp, InMacro, Sp, naturals, Comma, Sp,
            left, Comma, Sp, right, Sp, InMacro, Sp, integers, Comma,
            RowBreak, Grp(),
            prime, Sp, Eq, Sp, witnessPrime, Sp, Land, Sp,
            order, Sp, Eq, Sp, witnessOrder, Sp, Land, Sp,
            left, Sp, Eq, Sp, witnessLeft, Sp, Land, Sp,
            right, Sp, Eq, Sp, witnessRight, Sp, Land, RowBreak, Grp(),
            D(1), Sp, Leq, Sp, order, Sp, Land, Sp,
            CollisionConditions(prime, order, left, right), Sp, Land, RowBreak, Grp(),
            Valuation(prime, left, right), Sp, Eq, Sp, order);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Open, general, Close, Sp, Land, RowBreak, Grp(),
            Open, witness, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
