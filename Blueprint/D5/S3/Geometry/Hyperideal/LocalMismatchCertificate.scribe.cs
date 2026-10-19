using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class LocalMismatchCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Geometry/Hyperideal/LocalMismatchCertificate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact local certificate permits different flat pi-edge labels on equal "
            + "shared-face lengths.",
        H("A local flat mismatch certificate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("local-mismatch-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The forbidden local certificate"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Use the coordinate order (12, 13, 14, 34, 24, 23). The first "
                        + "vector is (2,2,2,20,2,2) and the second is (2,2,2,2,20,2). "
                        + "The shared face 123 therefore has the same three cosine "
                        + "lengths on both sides, while the selected flat pi pairs are "
                        + "(12,34) and (13,24). The claim says that this complete finite "
                        + "certificate cannot occur."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("local-mismatch-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The finite mismatch certificate"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The three shared coordinates agree and the two pair labels "
                            + "are different. For the selected edge in each orientation, "
                            + "the original cosine is -4/3, with denominator 27 and "
                            + "numerator -36. After orienting the long edge first, the "
                            + "original cosine is -10/9, with denominator 567 and "
                            + "numerator -630. The strict length comparison uses "
                            + "cosh(2 arccosh 2)=7<8. This is a local arithmetic "
                            + "certificate; it makes no claim about global face pairing, "
                            + "edge degree, total angle, or a closed CFMP realization."))),
                DescribeRole.Theorem))));

    private static Formula ClaimFormula() =>
        Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff,
            Not(WitnessFormula())));

    private static Formula WitnessFormula()
    {
        var s0 = Call("sigma", D(0));
        var s1 = Call("sigma", D(1));
        var s2 = Call("sigma", D(2));
        var s3 = Call("sigma", D(3));
        var s4 = Call("sigma", D(4));
        var s5 = Call("sigma", D(5));
        var t0 = Call("tau", D(0));
        var t1 = Call("tau", D(1));
        var t2 = Call("tau", D(2));
        var t3 = Call("tau", D(3));
        var t4 = Call("tau", D(4));
        var t5 = Call("tau", D(5));
        var minusFourThirds = new Formula.Negate(Fraction(F.D(4), F.D(3)));
        var minusTenNinths = new Formula.Negate(Fraction(F.D(1, 0), F.D(9)));
        return And(
            Eq(s0, t0),
            Eq(s1, t1),
            Eq(s5, t5),
            Not(Eq(Call("sigmaPi"), Call("tauPi"))),
            Eq(Call("cosine", s0, s1, s2, s3, s4, s5), minusFourThirds),
            Eq(Call("cosine", t0, t1, t2, t4, t3, t5), minusFourThirds),
            Eq(Call("cosine", F.D(2, 0), D(2), D(2), D(2), D(2), D(2)), minusTenNinths),
            Lt(D(7), D(8)));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);

    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Not(Formula value) => new Formula.Not(value);

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula And(params Formula[] parts)
    {
        var result = parts[^1];
        for (var i = parts.Length - 2; i >= 0; i--)
            result = new Formula.Logic(parts[i], FormulaLogicOperator.And, result);
        return result;
    }
}
