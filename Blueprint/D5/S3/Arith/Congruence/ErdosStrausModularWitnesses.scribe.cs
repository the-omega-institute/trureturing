using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class ErdosStrausModularWitnessesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Five modular families have explicit positive Erdos--Straus witnesses.",
        H("Erdos--Straus Modular Witnesses"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("erdos-straus-modular-witnesses"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Congruence/ErdosStrausModularWitnesses."
                        + "erdos_straus_modular_witnesses"),
                H("Five congruence families admit explicit reciprocal decompositions"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Write a positive even integer as 2q and a positive multiple of three "
                            + "as 3q. Their displayed denominator triples are positive and solve "
                            + "four over n as a sum of three unit fractions.")),
                    Paragraph(Text(
                        "For arbitrary k, the constructions also solve the classes 3k+2, 4k+3, "
                            + "and 8k+5. Positivity is part of the witness predicate, so none of "
                            + "the rational divisions uses a zero denominator.")),
                    Paragraph(Text(
                        "The three final clauses verify the concrete triples (1,2,2), (2,5,10), "
                            + "and (2,28,28) for n equal to 2, 5, and 7."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula q = F.Id("q");
        Formula k = F.Id("k");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula W(Formula n, Formula x, Formula y, Formula z) =>
            Call("IsErdosStrausWitness", n, x, y, z);
        Formula Add(Formula left, Formula right) =>
            Seq(left, Sp, Plus, Sp, right);
        Formula Mul(Formula left, Formula right) =>
            Seq(left, Sp, Times, Sp, right);
        Formula Paren(Formula value) => Seq(Open, value, Close);
        Formula ForPositiveQ(Formula body) => Seq(
            Open, Forall, Sp, q, Colon, Sp, naturals, Comma, Sp,
            D(0), Sp, Lt, Sp, q, Sp, Rightarrow, Sp, body, Close);
        Formula ForK(Formula body) => Seq(
            Open, Forall, Sp, k, Colon, Sp, naturals, Comma, Sp, body, Close);

        Formula even = ForPositiveQ(W(Mul(D(2), q), q, Mul(D(2), q), Mul(D(2), q)));
        Formula triple = ForPositiveQ(W(
            Mul(D(3), q), q, Mul(D(4), q), Mul(D(1, 2), q)));
        Formula modThreeN = Add(Mul(D(3), k), D(2));
        Formula kPlusOne = Add(k, D(1));
        Formula modThree = ForK(W(
            modThreeN, kPlusOne, modThreeN, Mul(Paren(modThreeN), Paren(kPlusOne))));
        Formula modFourN = Add(Mul(D(4), k), D(3));
        Formula modFourDenominator = Mul(
            Mul(D(2), Paren(modFourN)), Paren(kPlusOne));
        Formula modFour = ForK(W(
            modFourN, kPlusOne, modFourDenominator, modFourDenominator));
        Formula modEightN = Add(Mul(D(8), k), D(5));
        Formula modEight = ForK(W(
            modEightN,
            Add(Mul(D(2), k), D(2)),
            Mul(Paren(modEightN), Paren(kPlusOne)),
            Mul(Mul(D(2), Paren(modEightN)), Paren(kPlusOne))));

        return Disp(new Formula.Aligned([
            Seq(even, Sp, Land),
            Seq(Grp(), triple, Sp, Land),
            Seq(Grp(), modThree, Sp, Land),
            Seq(Grp(), modFour, Sp, Land),
            Seq(Grp(), modEight, Sp, Land),
            Seq(Grp(), W(D(2), D(1), D(2), D(2)), Sp, Land),
            Seq(Grp(), W(D(5), D(2), D(5), D(1, 0)), Sp, Land),
            Seq(Grp(), W(D(7), D(2), D(2, 8), D(2, 8)), Dot),
        ]));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var item = 0; item < arguments.Length; item++)
        {
            if (item > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[item]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}
