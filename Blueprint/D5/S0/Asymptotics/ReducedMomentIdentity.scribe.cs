using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics;

internal sealed class ReducedMomentIdentityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deleting one index converts its gap-weighted moment into a difference of two "
            + "power sums, either over the reduced set or, under membership, the full set.",
        H("Reduced Moment Identities"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reduced-moment-identity-erased"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/ReducedMomentIdentity.reducedMoment_eq"),
                H("Moment identity over the erased set"),
                StatementSource.FromAuthor(ReducedMomentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "After the distinguished index is erased, distributing each term "
                            + "turns the gap-weighted moment into the distinguished value "
                            + "times the next power sum minus the following power sum.")),
                    Paragraph(Text(
                        "The proposition motivating this statement appeared in commentary "
                            + "with positivity and order assumptions. This algebraic identity "
                            + "itself requires neither of those assumptions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reduced-moment-identity-member"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/ReducedMomentIdentity.reducedMoment_eq_of_mem"),
                H("Moment identity over the full set"),
                StatementSource.FromAuthor(ReducedMomentOfMemFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "When the distinguished index belongs to the finite set, its gap is "
                            + "zero, so its summand contributes nothing and may be inserted "
                            + "into or removed from the sum.")),
                    Paragraph(Text(
                        "For every other index, distributivity and the successor rules for "
                            + "powers reduce the summand to the displayed difference of full "
                            + "power sums."))),
                DescribeRole.Theorem))));

    private static Formula ReducedMomentFormula()
    {
        Formula iota = F.Id("iota");
        Formula ring = F.Id("R");
        Formula set = F.Id("S");
        Formula index = F.Id("i");
        Formula values = F.Id("x");
        Formula degree = F.Id("n");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Context(iota, ring),
            Parameters(iota, ring, set, index, values, degree),
            Moment(set, index, values, degree), Sp, Eq, Sp,
            PowerSumDifference(Erase(set, index), index, values, degree), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula ReducedMomentOfMemFormula()
    {
        Formula iota = F.Id("iota");
        Formula ring = F.Id("R");
        Formula set = F.Id("S");
        Formula index = F.Id("i");
        Formula values = F.Id("x");
        Formula degree = F.Id("n");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Context(iota, ring),
            Parameters(iota, ring, set, index, values, degree),
            index, Sp, InMacro, Sp, set, Sp, Implies, RowBreak,
            Moment(set, index, values, degree), Sp, Eq, Sp,
            PowerSumDifference(set, index, values, degree), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Context(Formula iota, Formula ring) =>
        Seq(
            Forall, Sp, iota, Colon, Sp, F.Id("Type"), Comma, Sp,
            TypeClass(Call("DecidableEq", iota)), Comma, RowBreak,
            Forall, Sp, ring, Colon, Sp, F.Id("Type"), Comma, Sp,
            TypeClass(Call("CommRing", ring)), Comma, RowBreak);

    private static Formula Parameters(
        Formula iota,
        Formula ring,
        Formula set,
        Formula index,
        Formula values,
        Formula degree) =>
        Seq(
            Forall, Sp, set, Colon, Sp, Call("Finset", iota), Comma, Sp,
            index, Colon, Sp, iota, Comma, RowBreak,
            values, Colon, Sp, iota, Sp, To, Sp, ring, Comma, Sp,
            degree, Colon, Sp, NaturalNumbers(), Comma, RowBreak);

    private static Formula Moment(
        Formula set,
        Formula index,
        Formula values,
        Formula degree)
    {
        Formula summationIndex = F.Id("j");
        Formula value = Apply(values, summationIndex);
        Formula gap = Seq(
            Apply(values, index), Sp, Minus, Sp, value);
        Formula term = Seq(
            value, Sp, Cdot, Sp, Grp(gap), Sp, Cdot, Sp,
            Power(value, degree));

        return FiniteSum(summationIndex, Erase(set, index), term);
    }

    private static Formula PowerSumDifference(
        Formula set,
        Formula index,
        Formula values,
        Formula degree)
    {
        Formula summationIndex = F.Id("j");
        Formula value = Apply(values, summationIndex);
        Formula next = Seq(degree, Sp, Plus, Sp, Num(1));
        Formula following = Seq(degree, Sp, Plus, Sp, Num(2));

        return Seq(
            Apply(values, index), Sp, Cdot, Sp,
            FiniteSum(summationIndex, set, Power(value, next)), Sp, Minus, Sp,
            FiniteSum(summationIndex, set, Power(value, following)));
    }

    private static Formula FiniteSum(Formula index, Formula set, Formula term) =>
        Seq(Sum, Underscore, Grp(index, Sp, InMacro, Sp, set), Sp, term);

    private static Formula Erase(Formula set, Formula index) =>
        Call("erase", set, index);

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula NaturalNumbers() =>
        Seq(Mathbb, Grp(F.Id("N")));

    private static Formula TypeClass(Formula value) =>
        Seq(OpenBracket, value, CloseBracket);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
}
