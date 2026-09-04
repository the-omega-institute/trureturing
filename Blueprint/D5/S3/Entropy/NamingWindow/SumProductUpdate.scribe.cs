using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.NamingWindow;

internal sealed class SumProductUpdateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A public, commutative-semiring form of the coordinate sum-product identity.",
        H("Coordinate Sum-Product Update"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sum-product-update"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/NamingWindow/SumProductUpdate.sum_prod_update"),
                H("A distinguished coordinate factors from the assignment sum"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Summing over every assignment the product of all coordinates except "
                            + "one, times a factor at that one coordinate, factors into the "
                            + "product of the other coordinates' sums times the sum of that "
                            + "factor.")),
                    Paragraph(Text(
                        "The value here is an API one, not mathematical novelty. The identity "
                            + "follows from the distributive law for finite products of sums; "
                            + "what the repository lacked was a public name for it.")),
                    Paragraph(Text(
                        "Three frozen modules in this directory each carry a private copy of "
                            + "this exact statement. Two record in their headers that they "
                            + "re-prove it because the earlier copies are \"private and not "
                            + "reusable public theorems\". Those three are frozen and therefore "
                            + "cannot import this module: naming the fact here does not remove "
                            + "them; it stops the next copy.")),
                    Paragraph(Text(
                        "The frozen copies fix the codomain to the reals, while the argument "
                            + "needs no subtraction, division, or order. The public statement is "
                            + "therefore given over an arbitrary commutative semiring."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula iota = F.Id("iota");
        Formula alphabet = F.Id("O");
        Formula ring = F.Id("R");
        Formula family = F.Id("p");
        Formula distinguished = F.Id("i");
        Formula factor = F.Id("g");
        Formula assignment = F.Id("u");
        Formula coordinate = F.Id("j");
        Formula letter = F.Id("a");
        Formula erased = Call("erase", F.Id("univ"), distinguished);

        Formula assignmentType = Arrow(iota, alphabet);
        Formula familyType = Arrow(iota, Arrow(alphabet, ring));
        Formula factorType = Arrow(alphabet, ring);
        Formula otherCoordinateTerm = Apply(
            Apply(family, coordinate),
            Apply(assignment, coordinate));
        Formula left = Seq(
            Sum, Underscore, Grp(Typed(assignment, assignmentType)), Sp,
            Grp(FiniteProduct(coordinate, erased, otherCoordinateTerm)), Sp, Times, Sp,
            Apply(factor, Apply(assignment, distinguished)));
        Formula coordinateSum = Seq(
            Sum, Underscore, Grp(Typed(letter, alphabet)), Sp,
            Apply(Apply(family, coordinate), letter));
        Formula right = Seq(
            Grp(FiniteProduct(coordinate, erased, coordinateSum)), Sp, Times, Sp,
            Sum, Underscore, Grp(Typed(letter, alphabet)), Sp, Apply(factor, letter));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, iota, Colon, Sp, F.Id("Type"), Comma, Sp,
            TypeClass(Call("Fintype", iota)), Comma, Sp,
            TypeClass(Call("DecidableEq", iota)), Comma, RowBreak,
            Forall, Sp, alphabet, Colon, Sp, F.Id("Type"), Comma, Sp,
            TypeClass(Call("Fintype", alphabet)), Comma, RowBreak,
            Forall, Sp, ring, Colon, Sp, F.Id("Type"), Comma, Sp,
            TypeClass(Call("CommSemiring", ring)), Comma, RowBreak,
            Forall, Sp, family, Colon, Sp, familyType, Comma, Sp,
            distinguished, Colon, Sp, iota, Comma, Sp,
            factor, Colon, Sp, factorType, Comma, RowBreak,
            left, Sp, Eq, Sp, right, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula FiniteProduct(Formula index, Formula set, Formula term) =>
        Seq(Prod, Underscore, Grp(index, Sp, InMacro, Sp, set), Sp, term);

    private static Formula TypeClass(Formula value) =>
        Seq(OpenBracket, value, CloseBracket);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
}
