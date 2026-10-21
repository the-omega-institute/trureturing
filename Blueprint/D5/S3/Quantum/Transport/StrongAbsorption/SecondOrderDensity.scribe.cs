using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Transport.StrongAbsorption;

internal sealed class SecondOrderDensityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "SecondOrderDensity for strong-absorption moments.",
        H("SecondOrderDensity"),
        Blocks(
            Paragraph(Text("Real arithmetic is used in all coefficients. Integrals without an explicit measure use volume. M is the channel count; n is the moment order.")),
            Describe.Lean(DescribeId.Create("quadraticdensitypoly"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/SecondOrderDensity.quadraticDensityPoly"),
                H("quadraticDensityPoly"), StatementSource.FromAuthor(Disp(Statement0())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity is used to evaluate the strong-absorption coefficients."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("law-polynomial-secondorder"),
                DeclarationHandle.Create("D5/S3/Quantum/Transport/StrongAbsorption/SecondOrderDensity.law_polynomial_secondOrder"),
                H("law_polynomial_secondOrder"), StatementSource.FromAuthor(Disp(Statement1())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed identity is used to evaluate the strong-absorption coefficients."))), DescribeRole.Theorem)
        )));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula CastM() => Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))));
    private static Formula V(string name) => F.Id(name);
    private static Formula Qualified(params string[] names)
    {
        var items = new List<Formula>();
        foreach (var name in names)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(Seq(Operatorname, Grp(V(name))));
        }
        return Seq([.. items]);
    }
    private static Formula Sup(Formula value) => Seq(Caret, Grp(value));

    private static Formula Statement0() =>
        Seq(Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(V("quadraticDensityPoly"), Sp, V("M"), Sp, Eq, Sp, Parenthesized(Seq(V("C"), Sp, Parenthesized(Seq(Seq(D(1), Sp, Slash, Sp, D(2)), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("R")))))), Sp, Cdot, Sp, Parenthesized(Seq(new Formula.Power(Parenthesized(Parenthesized(Seq(V("linearDensityPoly"), Sp, V("M")))), D(2)), Sp, Minus, Sp, V("C"), Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("R")))))), Sp, Cdot, Sp, Parenthesized(Seq(Parenthesized(Seq(Sum, Sp, V("i"), Sp, Colon, Sp, V("Fin"), Sp, V("M"), Sp, Comma, Sp, new Formula.Power(Parenthesized(Parenthesized(Seq(V("X"), Sp, Parenthesized(Seq(Qualified("Sum","inl"), Sp, V("i")))))), D(2)))), Sp, Plus, Sp, Parenthesized(Seq(Sum, Sp, V("j"), Sp, Colon, Sp, V("Fin"), Sp, V("M"), Sp, Comma, Sp, new Formula.Power(Parenthesized(Parenthesized(Seq(V("X"), Sp, Parenthesized(Seq(Qualified("Sum","inr"), Sp, V("j")))))), D(2)))))), Sp, Plus, Sp, V("C"), Sp, D(2), Sp, Cdot, Sp, Parenthesized(Seq(Sum, Sp, V("i"), Sp, Colon, Sp, V("Fin"), Sp, V("M"), Sp, Comma, Sp, V("X"), Sp, Parenthesized(Seq(Qualified("Sum","inl"), Sp, V("i"))))), Sp, Cdot, Sp, Parenthesized(Seq(Sum, Sp, V("j"), Sp, Colon, Sp, V("Fin"), Sp, V("M"), Sp, Comma, Sp, V("X"), Sp, Parenthesized(Seq(Qualified("Sum","inr"), Sp, V("j")))))))))))));

    private static Formula Statement1() =>
        Seq(Seq(Forall, Sp, Parenthesized(Seq(V("M"), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("N"))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Parenthesized(Seq(D(1), Sp, Le, Sp, V("M")))), Sp, To, Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Parenthesized(Seq(Parenthesized(Seq(Int, Sp, V("p"), Sp, Comma, Sp, V("baseWeight"), Sp, V("M"), Sp, CastM(), Sp, V("p"), Sp, Cdot, Sp, V("eval"), Sp, Parenthesized(Seq(Qualified("Sum","elim"), Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("p"), Sp, Dot, Sp, D(2))), Sp, Parenthesized(Seq(V("quadraticDensityPoly"), Sp, V("M"))))), Sp, Eq, Sp, D(0)))), Sp, To, Sp, Parenthesized(Parenthesized(Seq(Seq(Forall, Sp, Parenthesized(Seq(V("P"), Sp, Colon, Sp, Parenthesized(Seq(V("MvPolynomial"), Sp, Parenthesized(Seq(V("Sum"), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))), Sp, Parenthesized(Seq(V("Fin"), Sp, V("M"))))), Sp, Seq(Mathbb, Grp(V("R")))))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Seq(Seq(V("fun"), Sp, GammaLower), Sp, Mapsto, Sp, Parenthesized(Seq(Parenthesized(Seq(Int, Sp, V("p"), Sp, Comma, Sp, V("eval"), Sp, Parenthesized(Seq(Qualified("Sum","elim"), Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("p"), Sp, Dot, Sp, D(2))), Sp, V("P"), Sp, Seq(Thin, V("d")), Sp, V("law"), Sp, V("M"), Sp, GammaLower)), Sp, Minus, Sp, Parenthesized(Seq(Int, Sp, V("p"), Sp, Comma, Sp, V("baseWeight"), Sp, V("M"), Sp, CastM(), Sp, V("p"), Sp, Cdot, Sp, V("eval"), Sp, Parenthesized(Seq(Qualified("Sum","elim"), Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("p"), Sp, Dot, Sp, D(2))), Sp, V("P"))), Sp, Slash, Sp, new Formula.Power(Parenthesized(Parenthesized(Seq(V("partition"), Sp, V("M"), Sp, CastM()))), D(2)), Sp, Minus, Sp, new Formula.Power(Parenthesized(GammaLower), Seq(Minus, D(1))), Sp, Cdot, Sp, Parenthesized(Seq(Parenthesized(Seq(Int, Sp, V("p"), Sp, Comma, Sp, V("baseWeight"), Sp, V("M"), Sp, CastM(), Sp, V("p"), Sp, Cdot, Sp, V("eval"), Sp, Parenthesized(Seq(Qualified("Sum","elim"), Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("p"), Sp, Dot, Sp, D(2))), Sp, Parenthesized(Seq(V("P"), Sp, Cdot, Sp, V("linearDensityPoly"), Sp, V("M"))))), Sp, Slash, Sp, new Formula.Power(Parenthesized(Parenthesized(Seq(V("partition"), Sp, V("M"), Sp, CastM()))), D(2)))), Sp, Minus, Sp, new Formula.Power(Parenthesized(new Formula.Power(Parenthesized(GammaLower), Seq(Minus, D(1)))), D(2)), Sp, Cdot, Sp, Parenthesized(Seq(Parenthesized(Seq(Int, Sp, V("p"), Sp, Comma, Sp, V("baseWeight"), Sp, V("M"), Sp, CastM(), Sp, V("p"), Sp, Cdot, Sp, V("eval"), Sp, Parenthesized(Seq(Qualified("Sum","elim"), Sp, V("p"), Sp, Dot, Sp, D(1), Sp, V("p"), Sp, Dot, Sp, D(2))), Sp, Parenthesized(Seq(V("P"), Sp, Cdot, Sp, V("quadraticDensityPoly"), Sp, V("M"))))), Sp, Slash, Sp, new Formula.Power(Parenthesized(Parenthesized(Seq(V("partition"), Sp, V("M"), Sp, CastM()))), D(2)))))))), Sp, Seq(Eq, Sup(V("O"))), Sp, OpenBracket, Sp, V("atTop"), Sp, CloseBracket, Sp, Parenthesized(Seq(Seq(Seq(V("fun"), Sp, GammaLower), Sp, Colon, Sp, Parenthesized(Seq(Mathbb, Grp(V("R"))))), Sp, Mapsto, Sp, Parenthesized(new Formula.Power(Parenthesized(new Formula.Power(Parenthesized(GammaLower), Seq(Minus, D(1)))), D(3))))))))))))))))));
}
