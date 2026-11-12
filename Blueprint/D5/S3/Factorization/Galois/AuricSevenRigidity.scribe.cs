using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois;

internal sealed class AuricSevenRigidityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/Galois/AuricSevenRigidity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The zero-product tensor endpoint forces homothety of two actual field spans.",
        H("The zero-product tensor endpoint"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("auric-seven-rigidity-zero-product-tensor-homothety"),
                DeclarationHandle.Create(Prefix + "zero_product_tensor_homothety"),
                H("Zero-product tensor homothety"),
                StatementSource.FromAuthor(Disp(HomothetyFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For fields F and D with an F-algebra structure, the three actual "
                    + "zero-product identities u₁p=u₃s and u₁q=−u₂s, with u₁ and s nonzero, "
                    + "identify the span of p,q,s with the image of the span of u₁,u₂,u₃ "
                    + "under multiplication by the original element s/u₁. This is the "
                    + "endpoint calculation used after the adjugate coefficient comparison; "
                    + "the preceding degree-seven contraction classification remains a separate "
                    + "obligation of the full source lemma."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("auric-seven-rigidity-zero-product-tensor-homothety-nonzero"),
                DeclarationHandle.Create(Prefix + "zero_product_tensor_homothety_nonzero"),
                H("Nonzero homothety witness"),
                StatementSource.FromAuthor(Disp(NonzeroFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The same calculation packages the multiplier as an explicit nonzero "
                    + "element of D. This declaration is a consumed witness for the preceding "
                    + "endpoint theorem, rather than an independent classification claim."))),
                DescribeRole.Theorem)),
        []));

    private static Formula HomothetyFormula()
    {
        Formula u1 = I("u1"), u2 = I("u2"), u3 = I("u3");
        Formula p = I("p"), q = I("q"), s = I("s"), f = I("F");
        Formula hypotheses = And(Neq(u1, Zero()), And(Neq(s, Zero()),
            And(Eq(Mul(u1, p), Mul(u3, s)), Eq(Mul(u1, q), Neg(Mul(u2, s))))));
        Formula conclusion = Eq(Span(f, Set3(p, q, s)),
            Map(f, MulLeft(f, Div(s, u1)), Span(f, Set3(u1, u2, u3))));
        Formula quantified = Imp(hypotheses, conclusion);
        foreach (string name in new[] { "s", "q", "p", "u3", "u2", "u1" })
            quantified = All(name, I("D"), quantified);
        Formula fields = Inst(Call("Algebra", I("F"), I("D")), quantified);
        fields = Inst(Call("Field", I("D")), fields);
        fields = Inst(Call("Field", I("F")), fields);
        return All("F", Ty(), All("D", Ty(), fields));
    }

    private static Formula NonzeroFormula()
    {
        Formula u1 = I("u1"), u2 = I("u2"), u3 = I("u3");
        Formula p = I("p"), q = I("q"), s = I("s"), f = I("F"), gamma = I("gamma");
        Formula hypotheses = And(Neq(u1, Zero()), And(Neq(s, Zero()),
            And(Eq(Mul(u1, p), Mul(u3, s)), Eq(Mul(u1, q), Neg(Mul(u2, s))))));
        Formula conclusion = Some("gamma", I("D"), And(Neq(gamma, Zero()),
            Eq(Span(f, Set3(p, q, s)),
                Map(f, MulLeft(f, gamma), Span(f, Set3(u1, u2, u3))))));
        Formula quantified = Imp(hypotheses, conclusion);
        foreach (string name in new[] { "s", "q", "p", "u3", "u2", "u1" })
            quantified = All(name, I("D"), quantified);
        Formula fields = Inst(Call("Algebra", I("F"), I("D")), quantified);
        fields = Inst(Call("Field", I("D")), fields);
        fields = Inst(Call("Field", I("F")), fields);
        return All("F", Ty(), All("D", Ty(), fields));
    }

    private static Formula Span(Formula field, Formula set) => Call("Submodule.span", field, set);
    private static Formula Map(Formula field, Formula map, Formula submodule) => Call("Submodule.map", map, submodule);
    private static Formula MulLeft(Formula field, Formula a) => Call("LinearMap.mulLeft", field, a);
    private static Formula Set3(Formula a, Formula b, Formula c) => Seq(OpenBrace, a, Comma, Sp, b, Comma, Sp, c, CloseBrace);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Qualified(name), [.. args]);
    private static Formula Qualified(string name)
    {
        var items = new System.Collections.Generic.List<Formula> { Operatorname, Grp(I(name.Split('.')[0])) };
        foreach (string part in name.Split('.')[1..])
        {
            items.Add(Dot);
            items.Add(Operatorname);
            items.Add(Grp(I(part)));
        }
        return Seq([.. items]);
    }
    private static Formula I(string name) => F.Id(name);
    private static Formula Ty() => Seq(I("Type"), Star);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(I(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) => Seq(Exists, Sp, Parenthesized(Seq(I(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Inst(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Neq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Mul(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, b);
    private static Formula Div(Formula a, Formula b) => Seq(a, Sp, Slash, Sp, b);
    private static Formula Neg(Formula a) => Seq(Minus, a);
    private static Formula Zero() => D(0);
}
