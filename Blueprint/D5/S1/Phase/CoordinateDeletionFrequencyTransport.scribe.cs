using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase;

internal sealed class CoordinateDeletionFrequencyTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Transport finite-family coordinate frequencies and union closure through coordinate deletion.",
        H("Coordinate-Deletion Frequency Transport"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("quantitative-and-half-frequency-transport"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/CoordinateDeletionFrequencyTransport."
                    + "quantitative_and_half_frequency_transport"),
                H("Quantitative and half-frequency transport"),
                StatementSource.FromAuthor(QuantitativeTransportFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let G be the image of F after deleting D, and let N, M, x, and b "
                            + "be the displayed family and coordinate-frequency counts. The first "
                            + "inequality holds without assuming that F is union-closed.")),
                    Paragraph(Text(
                        "The proof injects each non-j deletion fibre into the powerset of D by "
                            + "sending A to its deleted trace A intersect D. Reconstruction from "
                            + "A minus D and A intersect D gives the fibre bound, while deletion "
                            + "outside j also gives b at most x.")),
                    Paragraph(Text(
                        "If j occurs in at least half of G, the same two live counting bounds give "
                            + "the stated (2^r+1) frequency bound in F. This is a transport theorem "
                            + "and does not resolve the Frankl union-closed sets conjecture."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("union-closed-after-deletion"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/CoordinateDeletionFrequencyTransport."
                    + "union_closed_after_deletion"),
                H("Coordinate deletion preserves union closure"),
                StatementSource.FromAuthor(UnionClosureFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For two members represented as A0 minus D and B0 minus D, their union is "
                        + "the deletion image of A0 union B0. This is the bind-only companion for "
                        + "the Frankl coordinate-deletion induction interface."))),
                DescribeRole.Theorem))));

    private static Formula QuantitativeTransportFormula()
    {
        Formula family = F.Id("F");
        Formula deleted = F.Id("D");
        Formula element = F.Id("j");
        Formula count = F.Id("r");
        Formula sourceCard = F.Id("N");
        Formula imageCard = F.Id("M");
        Formula sourceFrequency = F.Id("x");
        Formula imageFrequency = F.Id("b");
        Formula set = F.Id("A");
        Formula image = Image(family, deleted, set);
        Formula imageName = F.Id("G");
        Formula twoPower = Power(D(2), count);
        Formula imageDeficit = Parenthesized(Subtract(imageCard, imageFrequency));
        Formula weightedCoefficient = Parenthesized(Add(
            imageFrequency,
            Product(twoPower, imageDeficit)));
        Formula quantitativeClause = Parenthesized(Seq(
            Product(weightedCoefficient, sourceFrequency), Sp, Geq, Sp,
            Product(imageFrequency, sourceCard)));
        Formula halfClause = Parenthesized(Seq(
            Product(D(2), imageFrequency), Sp, Geq, Sp, imageCard, Sp,
            Rightarrow, Sp,
            Product(
                Parenthesized(Add(twoPower, D(1))),
                sourceFrequency),
            Sp, Geq, Sp, sourceCard));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Alpha, Colon, Sp, F.Id("Type"), Comma, Sp,
                Typeclass(Call("DecidableEq", Alpha)), Comma),
            Seq(
                Bound(family, Finset(Finset(Alpha))), Comma, Sp,
                Bound(deleted, Finset(Alpha)), Comma, Sp,
                Bound(element, Alpha), Comma, Sp,
                Bound(count, Naturals()), Comma),
            Seq(
                Parenthesized(Seq(Card(deleted), Sp, Eq, Sp, count)), Sp,
                Land, Sp, Neg, Sp,
                Parenthesized(Member(element, deleted)), Sp,
                Rightarrow, Sp),
            Seq(
                F.Text, Grp(F.Id("where")), Sp,
                imageName, Sp, Eq, Sp, image, Comma, Sp,
                sourceCard, Sp, Eq, Sp, Card(family), Comma, Sp,
                imageCard, Sp, Eq, Sp, Card(imageName), Comma),
            Seq(
                sourceFrequency, Sp, Eq, Sp,
                FilteredCard(F.Id("A"), family, element), Comma, Sp,
                imageFrequency, Sp, Eq, Sp,
                FilteredCard(F.Id("B"), imageName, element), Comma),
            Seq(
                quantitativeClause, Sp, Land, Sp, halfClause, Dot),
        ]));
    }

    private static Formula UnionClosureFormula()
    {
        Formula family = F.Id("F");
        Formula deleted = F.Id("D");
        Formula first = F.Id("A");
        Formula second = F.Id("B");
        Formula set = F.Id("S");
        Formula image = Image(family, deleted, set);
        Formula sourceClosure = Parenthesized(Seq(
            Forall, Sp, Bound(first, family), Comma, Sp,
            Forall, Sp, Bound(second, family), Comma, Sp,
            Member(Call("union", first, second), family)));
        Formula imageClosure = Seq(
            Forall, Sp, Bound(first, image), Comma, Sp,
            Forall, Sp, Bound(second, image), Comma, Sp,
            Member(Call("union", first, second), image), Dot);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Alpha, Colon, Sp, F.Id("Type"), Comma, Sp,
                Typeclass(Call("DecidableEq", Alpha)), Comma),
            Seq(
                Bound(family, Finset(Finset(Alpha))), Comma, Sp,
                Bound(deleted, Finset(Alpha)), Comma),
            Seq(sourceClosure, Sp, Rightarrow, Sp),
            imageClosure,
        ]));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Typeclass(Formula value) =>
        Seq(OpenBracket, value, CloseBracket);

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);

    private static Formula Bound(Formula variable, Formula domain) =>
        Seq(variable, Sp, InMacro, Sp, domain);

    private static Formula Naturals() =>
        Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Finset(Formula carrier) =>
        Call("Finset", carrier);

    private static Formula Member(Formula element, Formula set) =>
        Seq(element, Sp, InMacro, Sp, set);

    private static Formula Card(Formula set) =>
        Seq(Lvert, Sp, set, Sp, Rvert);

    private static Formula Add(Formula left, Formula right) =>
        Seq(left, Sp, Plus, Sp, right);

    private static Formula Subtract(Formula left, Formula right) =>
        Seq(left, Sp, Minus, Sp, right);

    private static Formula Product(Formula left, Formula right) =>
        Seq(left, Sp, Cdot, Sp, right);

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula Image(Formula family, Formula deleted, Formula set) =>
        Call(
            "image",
            Seq(set, Sp, Mapsto, Sp,
                Parenthesized(Seq(set, Sp, Setminus, Sp, deleted))),
            family);

    private static Formula FilteredCard(
        Formula set,
        Formula family,
        Formula element) =>
        Card(Seq(
            OpenBrace, set, Sp, Mid, Sp,
            Member(set, family), Sp, Land, Sp, Member(element, set),
            CloseBrace));
}
