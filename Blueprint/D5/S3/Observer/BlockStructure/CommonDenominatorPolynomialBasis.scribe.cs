using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.BlockStructure;

internal sealed class CommonDenominatorPolynomialBasisDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct finite Cayley scales give a common-denominator polynomial basis.",
        H("Common-Denominator Polynomial Basis"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("common-denominator-numerators-form-a-polynomial-basis"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/BlockStructure/CommonDenominatorPolynomialBasis."
                        + "common_denominator_polynomial_basis"),
                H("The common-denominator family is a basis"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The family is constructed from the supplied distinct nonzero complex "
                            + "parameters, their multiplicities, and the common polynomial "
                            + "denominator.")),
                    Paragraph(Text(
                        "A local affine transport of the Bernstein family proves independence "
                            + "within each scale. Uniqueness of partial fractions then separates "
                            + "the scale blocks.")),
                    Paragraph(Text(
                        "The reference block supplies the remaining top degrees. Independence "
                            + "and the matching finite dimension identify the span with the full "
                            + "bounded-degree polynomial subspace."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula polynomial = Call("Polynomial", complex);
        Formula m = F.Id("m");
        Formula r = F.Id("r");
        Formula depth = F.Id("depth");
        Formula referenceDepth = F.Id("referenceDepth");
        Formula i = F.Id("i");
        Formula k = F.Id("k");
        Formula j = F.Id("j");
        Formula multiplicity = F.Id("multiplicity");
        Formula q = F.Id("q");
        Formula factor = F.Id("factor");
        Formula denominator = F.Id("D");
        Formula index = F.Id("I");
        Formula family = F.Id("p");
        Formula finM = Call("Fin", m);
        Formula rType = Arrow(finM, complex);
        Formula depthType = Arrow(finM, natural);

        Formula rNonzero = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", finM)],
            Seq(Apply(r, i), Sp, Neq, Sp, D(0)));
        Formula rInDisk = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", finM)],
            Seq(Call("norm", Apply(r, i)), Sp, Lt, Sp, D(1)));

        Formula multiplicityDefinition = Seq(
            Typed(multiplicity, depthType), Comma, Sp,
            Forall, Sp, Typed(i, finM), Comma, Sp,
            Apply(multiplicity, i), Sp, Eq, Sp,
            Apply(depth, i), Sp, Plus, Sp, D(1));
        Formula qDefinition = Seq(
            Typed(q, natural), Sp, Eq, Sp,
            Call("sum", finM, Lambda(Typed(i, finM), Apply(multiplicity, i))));
        Formula factorDefinition = Seq(
            Typed(factor, Arrow(finM, polynomial)), Comma, Sp,
            Forall, Sp, Typed(i, finM), Comma, Sp,
            Apply(factor, i), Sp, Eq, Sp,
            D(1), Sp, Plus, Sp,
            Call("C", Apply(r, i)), Sp, Cdot, Sp, F.Id("X"));
        Formula denominatorDefinition = Seq(
            Typed(denominator, polynomial), Sp, Eq, Sp,
            Call("prod", finM, Lambda(Typed(i, finM),
                Call("pow", Apply(factor, i), Apply(multiplicity, i)))));
        Formula sigmaIndex = Call("Sigma", finM,
            Lambda(Typed(i, finM), Call("Fin", Apply(multiplicity, i))));
        Formula referenceIndex = Call("Fin", Seq(referenceDepth, Sp, Plus, Sp, D(1)));
        Formula indexDefinition = Seq(
            Typed(index, Call("Type")), Sp, Eq, Sp,
            Call("Sum", sigmaIndex, referenceIndex));
        Formula nonreferenceValue = Seq(
            Call("pow", Seq(F.Id("X"), Sp, Plus, Sp, Call("C", Apply(r, i))), j),
            Sp, Cdot, Sp,
            Call("pow", Apply(factor, i),
                Seq(Apply(depth, i), Sp, Minus, Sp, j)),
            Sp, Cdot, Sp,
            Call("prodExcept", finM, i, Lambda(Typed(k, finM),
                Call("pow", Apply(factor, k), Apply(multiplicity, k)))));
        Formula familyDefinition = Seq(
            Typed(family, Arrow(index, polynomial)), Comma, Sp,
            Forall, Sp, Typed(i, finM), Comma, Sp,
            Typed(j, Call("Fin", Apply(multiplicity, i))), Comma, Sp,
            Apply(family, Call("inl", i, j)), Sp, Eq, Sp, nonreferenceValue,
            SemiSpace,
            Forall, Sp, Typed(j, referenceIndex), Comma, Sp,
            Apply(family, Call("inr", j)), Sp, Eq, Sp,
            denominator, Sp, Cdot, Sp, Call("pow", F.Id("X"), j));
        Formula letObjects = Seq(
            Operatorname, Grp(F.Id("let")), Open,
            multiplicityDefinition, SemiSpace,
            qDefinition, SemiSpace,
            factorDefinition, SemiSpace,
            denominatorDefinition, SemiSpace,
            indexDefinition, SemiSpace,
            familyDefinition, Close);
        Formula conclusion = Seq(
            Call("LinearIndependent", complex, family), Sp, Land, Sp,
            Call("span", complex, Call("range", family)), Sp, Eq, Sp,
            Call("degreeLT", complex,
                Seq(q, Sp, Plus, Sp, referenceDepth, Sp, Plus, Sp, D(1))));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Typed(m, natural), Comma, Sp,
                Typed(r, rType), Comma, Sp, Typed(depth, depthType), Comma),
            Seq(Typed(referenceDepth, natural), Comma),
            Seq(Typed(F.Id("rNonzero"), rNonzero), Comma, Sp,
                Typed(F.Id("rInjective"), Call("Injective", r)), Comma),
            Seq(Typed(F.Id("rInDisk"), rInDisk), Comma),
            Seq(letObjects, Comma),
            Seq(conclusion, Dot),
        ]));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var argument = 0; argument < arguments.Length; argument++)
        {
            if (argument > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[argument]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);
}
