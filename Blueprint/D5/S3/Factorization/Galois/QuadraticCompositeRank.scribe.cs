using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois;

internal sealed class QuadraticCompositeRankDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/Galois/QuadraticCompositeRank.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The concrete independent two-radical composite has rank four and Klein symmetry.",
        H("Quadratic Composite Rank"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rank-zero-case"),
                DeclarationHandle.Create(Prefix + "rank_zero_case"),
                H("The empty radical family is the trivial extension"),
                StatementSource.FromAuthor(RankZeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For r = 0 the field is Q itself, its degree is one, and its Galois "
                        + "group has one element. This explicitly audits the empty family."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rank-one-case"),
                DeclarationHandle.Create(Prefix + "rank_one_case"),
                H("One nonsquare radical gives a quadratic extension"),
                StatementSource.FromAuthor(RankOneFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The named SqrtTwoField is Mathlib's quadratic-algebra model of "
                        + "Q(sqrt 2). Its coordinate basis gives degree two, while identity "
                        + "and conjugation exhaust its two base automorphisms."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sqrt-two-sqrt-three-rank"),
                DeclarationHandle.Create(Prefix + "sqrt_two_sqrt_three_rank"),
                H("Two independent concrete radicals give degree four"),
                StatementSource.FromAuthor(RankTwoFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source theorem stated only its conclusions and supplied no "
                            + "premises. This formalization makes K = Q, r = 2, and the "
                            + "radicals 2 and 3 explicit.")),
                    Paragraph(Text(
                        "The private nonsquare proofs verify that 2 is not a square in Q "
                            + "and 3 is not a square in Q(sqrt 2). Mathlib's two quadratic "
                            + "ranks then multiply to four.")),
                    Paragraph(Text(
                        "Pinned Mathlib has no theorem for a square-class-independent "
                            + "family in K*/(K*)^2. General r is therefore not claimed; the "
                            + "mandatory r = 2 concrete case is complete."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sqrt-two-sqrt-three-galois-group"),
                DeclarationHandle.Create(Prefix + "sqrt_two_sqrt_three_galois_group"),
                H("The four base automorphisms form the Klein four-group"),
                StatementSource.FromAuthor(GaloisGroupFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Changing either radical's sign gives four distinct automorphisms. "
                            + "The degree bound proves there are no others, and their squares "
                            + "are identity. Mathlib's IsKleinFour classification supplies "
                            + "the multiplicative equivalence.")),
                    Paragraph(Text(
                        "Characteristic zero is used here to keep each root distinct from "
                            + "its negative. Primality of 2 and 3 is not a hypothesis; only "
                            + "the explicit nonsquare calculations carry the proof."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("square-radicand-independence-is-necessary"),
                DeclarationHandle.Create(
                    Prefix + "square_radicand_independence_is_necessary"),
                H("A square radicand makes the extension trivial"),
                StatementSource.FromAuthor(SquareRadicandFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a = 4, the chosen square root 2 already belongs to Q. Its adjoining "
                        + "field is the bottom field and has degree one rather than two. This "
                        + "is the r = 1 failure of square-class independence."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("square-class-independence-is-necessary"),
                DeclarationHandle.Create(
                    Prefix + "square_class_independence_is_necessary"),
                H("Radicals differing by a square factor collapse"),
                StatementSource.FromAuthor(RepeatedClassFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Inside Q(sqrt 2), the named sqrtEight is 2 sqrt 2 and squares to 8. "
                        + "Adjoining sqrt 2 and sqrt 8 therefore gives the same degree-two "
                        + "field, not degree four. This is the required sharpness witness."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("characteristic-two-sign-separation-is-necessary"),
                DeclarationHandle.Create(
                    Prefix + "characteristic_two_sign_separation_is_necessary"),
                H("Characteristic two identifies both sign choices"),
                StatementSource.FromAuthor(CharacteristicTwoFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In ZMod 2, one equals negative one and negation is the identity map. "
                        + "Thus the sign-change construction used to separate the four "
                        + "automorphisms cannot be transferred to characteristic two."))),
                DescribeRole.Lemma))));

    private static Formula Call(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(function), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));

    private static Formula CyclicTwo() => Seq(F.Id("C"), Underscore, Grp(D(2)));

    private static Formula RadicalField(Formula radicand) =>
        Seq(Rationals(), Open, Sqrt, Grp(radicand), Close);

    private static Formula CompositeField() =>
        Seq(Rationals(), Open, Sqrt, Grp(D(2)), Comma, Sp, Sqrt, Grp(D(3)), Close);

    private static Formula RepeatedClassField() =>
        Seq(Rationals(), Open, Sqrt, Grp(D(2)), Comma, Sp, Sqrt, Grp(D(8)), Close);

    private static Formula Degree(Formula extension, Formula basis) =>
        Seq(OpenBracket, extension, Colon, basis, CloseBracket);

    private static Formula Gal(Formula extension, Formula basis) =>
        Call(F.Id("Gal"), extension, basis);

    private static Formula Card(Formula value) => Seq(Lvert, value, Rvert);

    private static Formula RankZeroFormula()
    {
        Formula rationals = Rationals();
        return Disp(Seq(
            Degree(rationals, rationals), Sp, Eq, Sp, D(1), Sp, Land, Sp,
            Card(Gal(rationals, rationals)), Sp, Eq, Sp, D(1), Dot));
    }

    private static Formula RankOneFormula()
    {
        Formula rationals = Rationals();
        Formula field = RadicalField(D(2));
        return Disp(Seq(
            Degree(field, rationals), Sp, Eq, Sp, D(2), Sp, Land, Sp,
            Card(Gal(field, rationals)), Sp, Eq, Sp, D(2), Dot));
    }

    private static Formula RankTwoFormula()
    {
        Formula rationals = Rationals();
        return Disp(Seq(
            Degree(CompositeField(), rationals), Sp, Eq, Sp, D(4), Dot));
    }

    private static Formula GaloisGroupFormula()
    {
        Formula group = Seq(CyclicTwo(), Sp, Times, Sp, CyclicTwo());
        return Disp(Seq(Gal(CompositeField(), Rationals()), Sp, Sim, Sp, group, Dot));
    }

    private static Formula SquareRadicandFormula()
    {
        Formula degree = Degree(RadicalField(D(4)), Rationals());
        return Disp(Seq(
            degree, Sp, Eq, Sp, D(1), Sp, Land, Sp, degree, Sp, Neq, Sp, D(2), Dot));
    }

    private static Formula RepeatedClassFormula()
    {
        Formula degree = Degree(RepeatedClassField(), Rationals());
        return Disp(Seq(
            Sqrt, Grp(D(8)), Sp, Eq, Sp, D(2), Sqrt, Grp(D(2)), Comma, RowBreak,
            Grp(), degree, Sp, Eq, Sp, D(2), Sp, Land, Sp, degree, Sp, Neq, Sp, D(4), Dot));
    }

    private static Formula CharacteristicTwoFormula()
    {
        Formula field = Seq(Mathbb, Grp(F.Id("F"), Underscore, Grp(D(2))));
        return Disp(Seq(
            D(1), Sp, Eq, Sp, Minus, D(1), Sp, InMacro, Sp, field, Sp, Land, Sp,
            Call(F.Id("Negation"), field), Sp, Eq, Sp, F.Id("identity"), Dot));
    }
}
