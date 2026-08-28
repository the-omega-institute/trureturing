using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Submodularity;

internal sealed class ConditionalIndependentInformationSubmodularityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Entropy/Submodularity/ConditionalIndependentInformationSubmodularity."
            + "conditional_independent_information_submodular";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conditional product laws make finite selected information submodular.",
        H("Conditional-Independent Information Submodularity"),
        Blocks(Describe.Lean(
            DescribeId.Create("conditional-independent-information-submodular"),
            DeclarationHandle.Create(Declaration),
            H("Selected mutual information has diminishing returns"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A finite experiment index set carries finite dependent output types. "
                        + "For S contained in T and e outside T, the joint law is written on "
                        + "the tuple of outputs from S, the additional tuple from T minus S, "
                        + "the hidden state, and the output of e.")),
                Paragraph(Text(
                    "Conditional independence is stated on that joint law: at every active "
                        + "context consisting of the S-output tuple and hidden state, the joint "
                        + "conditional law of the remaining T-outputs and e factors as the "
                        + "product of its two marginals.")),
                Paragraph(Text(
                    "The four marginal laws constructed from the same joint mass are exactly "
                        + "the laws for S, S with e, T, and T with e. Their mutual-information "
                        + "increments satisfy the displayed diminishing-returns inequality.")),
                Paragraph(Text(
                    "The proof applies the finite mutual-information chain rule twice. The "
                        + "difference of conditional gains is the nonnegative conditional "
                        + "information between the remaining T-outputs and e given S, after "
                        + "the product-slice term is identified with zero."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Subscript(Formula value, Formula index) =>
        new Formula.Subscript(value, index);

    private static Formula And(params Formula[] formulas)
    {
        Formula result = formulas[^1];
        for (var index = formulas.Length - 2; index >= 0; index--)
            result = new Formula.Logic(formulas[index], FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula indexType = F.Id("I");
        Formula hidden = F.Id("X");
        Formula outputFamily = F.Id("Y");
        Formula smaller = F.Id("S");
        Formula larger = F.Id("T");
        Formula added = F.Id("e");
        Formula mass = F.Id("p");
        Formula tupleS = Subscript(outputFamily, smaller);
        Formula difference = Seq(larger, Sp, Setminus, Sp, smaller);
        Formula tupleDifference = Subscript(outputFamily, difference);
        Formula outputE = Subscript(outputFamily, added);
        Formula tupleSE = Subscript(outputFamily, Seq(Call("insert", added, smaller)));
        Formula tupleTE = Subscript(outputFamily, Seq(Call("insert", added, larger)));
        Formula pCarrier = Seq(
            tupleS, Sp, Times, Sp, Open, tupleDifference, Sp, Times, Sp,
            Open, hidden, Sp, Times, Sp, outputE, Close, Close);
        Formula context = Seq(Open, Subscript(F.Id("y"), smaller), Comma, Sp,
            F.Id("x"), Close);
        Formula remainingValue = Subscript(F.Id("y"), difference);
        Formula addedValue = Subscript(F.Id("y"), added);
        Formula conditional(Formula first, Formula? second = null) => Seq(
            mass, Open, first,
            second is null ? Seq() : Seq(Comma, Sp, second),
            Sp, Mid, Sp, context, Close);
        Formula conditionalProduct = Seq(
            conditional(remainingValue, addedValue), Sp, Eq, Sp,
            conditional(remainingValue), Sp, Times, Sp,
            conditional(addedValue));
        Formula information(Formula observed) =>
            Seq(Subscript(F.Id("I"), mass), Open, hidden, Comma, Sp, observed, Close);
        Formula smallerGain = Seq(
            information(tupleSE), Sp, Minus, Sp, information(tupleS));
        Formula largerGain = Seq(
            information(tupleTE), Sp, Minus, Sp,
            information(Subscript(outputFamily, larger)));
        Formula lawPremise = And(
            Call("Nonnegative", mass),
            Seq(Call("totalMass", mass), Sp, Eq, Sp, D(1)));
        Formula independencePremise = Seq(
            Forall, Sp, context, Comma, Sp,
            Call("active", mass, context), Sp, Rightarrow, Sp,
            conditionalProduct);
        Formula premises = And(
            Call("Finite", indexType),
            Call("Fintype", hidden),
            Call("Fintype", tupleS),
            Call("Fintype", tupleDifference),
            Call("Fintype", outputE),
            Seq(smaller, Sp, Subseteq, Sp, larger),
            new Formula.Not(Seq(added, Sp, InMacro, Sp, larger)),
            lawPremise,
            independencePremise);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("I", type),
                Bound("X", type),
                Bound("Y", Arrow(indexType, type)),
                Bound("S", Call("Finset", indexType)),
                Bound("T", Call("Finset", indexType)),
                Bound("e", indexType),
                Bound("p", Arrow(pCarrier, Seq(Mathbb, Grp(F.Id("R"))))),
            ],
            new Formula.Logic(
                premises,
                FormulaLogicOperator.Implies,
                Seq(smallerGain, Sp, Geq, Sp, largerGain))));
    }
}
