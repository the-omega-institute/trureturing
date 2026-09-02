using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Hankel;

internal sealed class GoldenTwoShadowBoundDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Hankel/GoldenTwoShadowBound.golden_two_shadow_bound";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A contractive Hankel map satisfies six equivalent golden-ratio Gram bounds.",
        H("Golden Two-Shadow Bound"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-two-shadow-bound"),
            DeclarationHandle.Create(Declaration),
            H("Six golden Gram criteria agree"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The positive operator D is constructed as the adjoint of the Hankel map "
                        + "composed with that map. Contractivity supplies the source positive-"
                        + "contraction scope.")),
                Paragraph(Text(
                    "The inverse criteria quantify units whose values are exactly I-D, so the "
                        + "display records invertibility together with each order bound."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula domain = F.Id("V");
        Formula codomain = F.Id("W");
        Formula hankel = F.Id("H");
        Formula gram = F.Id("D");
        Formula complement = F.Id("C");
        Formula type = Call("Type");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula identity = F.Id("I");
        Formula phi = new Formula.LatexMacro(FormulaLatexMacro.Phi);
        Formula phiInverse = Seq(phi, Caret, Grp(Minus, D(1)));
        Formula phiSquared = Seq(phi, Caret, Grp(D(2)));
        Formula mapType = Call("ContinuousLinearMap", complex, domain, codomain);
        Formula endomorphisms = Call("ContinuousLinearMap", complex, domain, domain);
        Formula gramSquare = Seq(gram, Caret, Grp(D(2)));
        Formula gramConstruction = Seq(
            hankel, Caret, Grp(Star), Sp, Circ, Sp, hankel);
        Formula complementValue = Call("val", complement);
        Formula inverseValue = Call(
            "val", Seq(complement, Caret, Grp(Minus, D(1))));
        Formula unitType = Call("Units", endomorphisms);
        Formula phiSquaredIdentity = Call(
            "algebraMap", real, endomorphisms, phiSquared);
        Formula phiIdentity = Call("algebraMap", real, endomorphisms, phi);

        Formula first = LessOrEqual(gramSquare, Subtract(identity, gram));
        Formula second = LessOrEqual(Add(gram, gramSquare), identity);
        Formula third = LessOrEqual(new Formula.Norm(gram), phiInverse);
        Formula fourth = LessOrEqual(
            new Formula.Norm(hankel), Seq(Sqrt, Grp(phiInverse)));
        Formula fifth = Seq(
            Exists, Sp, Typed(complement, unitType), Comma, Sp,
            Equal(complementValue, Subtract(identity, gram)), Sp, Land, Sp,
            LessOrEqual(inverseValue, phiSquaredIdentity));
        Formula sixth = Seq(
            Exists, Sp, Typed(complement, unitType), Comma, Sp,
            Equal(complementValue, Subtract(identity, gram)), Sp, Land, Sp,
            LessOrEqual(Multiply(gram, inverseValue), phiIdentity));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(Seq(domain, Comma, Sp, codomain), type), Comma),
            Seq(
                Grp(), Typeclass("NormedAddCommGroup", domain), Sp, Land, Sp,
                Typeclass("InnerProductSpace", complex, domain), Sp, Land, Sp,
                Typeclass("CompleteSpace", domain), Comma),
            Seq(
                Grp(), Typeclass("NormedAddCommGroup", codomain), Sp, Land, Sp,
                Typeclass("InnerProductSpace", complex, codomain), Sp, Land, Sp,
                Typeclass("CompleteSpace", codomain), Comma),
            Seq(
                Forall, Sp, Typed(hankel, mapType), Comma, Sp,
                new Formula.Norm(hankel), Sp, Leq, Sp, D(1), Sp,
                Rightarrow),
            Seq(
                Grp(), F.Id("let"), Sp, gram, Colon, Sp, endomorphisms,
                Sp, Eq, Sp, gramConstruction, Semi),
            Seq(Grp(), first, Sp, Iff, Sp, second, Sp, Iff, Sp, third),
            Seq(Grp(), Iff, Sp, fourth, Sp, Iff, Sp, fifth),
            Seq(Grp(), Iff, Sp, sixth, Dot),
        ]));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Typeclass(string name, params Formula[] arguments) =>
        Seq(OpenBracket, Call(name, arguments), CloseBracket);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.AddRange([Comma, Sp]);
            }

            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
