using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Submodularity;

internal sealed class CanonicalConditionalInformationSubmodularityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Entropy/Submodularity/CanonicalConditionalInformationSubmodularity."
            + "canonical_conditional_information_submodular";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conditional product laws make canonical selected-output information submodular.",
        H("Canonical Conditional Information Submodularity"),
        Blocks(Describe.Lean(
            DescribeId.Create("canonical-conditional-information-submodular"),
            DeclarationHandle.Create(Declaration),
            H("Canonical selected mutual information has diminishing returns"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let the hidden state and every output alphabet be finite. The joint "
                        + "mass is carried by the hidden state together with the exact "
                        + "dependent output tuple indexed by insert e T; the ambient index "
                        + "type itself need not be finite.")),
                Paragraph(Text(
                    "For S contained in T and e outside T, the canonical finite-set "
                        + "equivalences split the T-output tuple into the S outputs and the "
                        + "outputs indexed by T minus S, and split insert e T into the T "
                        + "outputs and the output at e.")),
                Paragraph(Text(
                    "The displayed context law is obtained from that same canonical mass. "
                        + "On each active context consisting of the S-output tuple and hidden "
                        + "state, the conditional law of the remaining T-outputs and the e "
                        + "output factors as the product of its two marginals.")),
                Paragraph(Text(
                    "The four explicitly typed selected marginals live on S, insert e S, T, "
                        + "and insert e T. Two finite mutual-information chain rules and the "
                        + "conditional product criterion yield the stated diminishing-return "
                        + "inequality."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Product(Formula left, Formula right) =>
        Seq(Open, left, Sp, Times, Sp, right, Close);

    private static Formula Subscript(Formula value, Formula index) =>
        new Formula.Subscript(value, index);

    private static Formula Define(Formula name, Formula type, Formula value) =>
        Seq(Typed(name, type), Sp, Colon, Eq, Sp, value);

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula indexType = F.Id("Index");
        Formula hiddenType = F.Id("Hidden");
        Formula outputFamily = F.Id("Output");
        Formula index = F.Id("i");
        Formula smaller = F.Id("S");
        Formula larger = F.Id("T");
        Formula added = F.Id("e");
        Formula mass = F.Id("p");
        Formula value = F.Id("z");
        Formula context = F.Id("c");
        Formula pair = F.Id("w");
        Formula difference = Seq(larger, Sp, Setminus, Sp, smaller);
        Formula insertedSmaller = Call("insert", added, smaller);
        Formula insertedLarger = Call("insert", added, larger);
        Formula outputAt(Formula selectedIndex) =>
            Apply(outputFamily, Call("val", selectedIndex));
        Formula tuple(Formula selected) => Seq(
            Open, Forall, Sp, Typed(index, selected), Comma, Sp,
            outputAt(index), Close);
        Formula tupleS = tuple(smaller);
        Formula tupleSE = tuple(insertedSmaller);
        Formula tupleT = tuple(larger);
        Formula tupleTE = tuple(insertedLarger);
        Formula tupleDifference = tuple(difference);
        Formula outputE = Apply(outputFamily, added);
        Formula lawCarrier(Formula selectedTuple) =>
            Arrow(Product(hiddenType, selectedTuple), real);
        Formula pCarrier = Product(hiddenType, tupleTE);
        Formula lawS = Subscript(mass, smaller);
        Formula lawSE = Subscript(mass, insertedSmaller);
        Formula lawT = Subscript(mass, larger);
        Formula lawTE = Subscript(mass, insertedLarger);
        Formula selectedMarginal(Formula selected) =>
            Call("selectedMarginal", mass, selected);
        Formula contextLaw = Subscript(mass, Seq(
            smaller, Comma, Sp, hiddenType, Semi, Sp, difference,
            Comma, Sp, added));
        Formula contextCarrier = Arrow(
            Product(Product(tupleS, hiddenType), Product(tupleDifference, outputE)),
            real);
        Formula conditionalLaw = Call("conditional", contextLaw, context);
        Formula marginalFirst = Apply(
            Call("marginal", conditionalLaw), Call("fst", pair));
        Formula swappedConditional = Call("swapLaw", conditionalLaw);
        Formula marginalSecond = Apply(
            Call("marginal", swappedConditional), Call("snd", pair));
        Formula factorized = Seq(
            conditionalLaw, Sp, Eq, Sp,
            Open, Typed(pair, Product(tupleDifference, outputE)), Sp,
            Mapsto, Sp, marginalFirst, Sp, Times, Sp, marginalSecond, Close);
        Formula finiteOutputs = Seq(
            Forall, Sp, Typed(index, indexType), Comma, Sp,
            Call("Fintype", Apply(outputFamily, index)));
        Formula nonnegative = Seq(
            Forall, Sp, Typed(value, pCarrier), Comma, Sp,
            D(0), Sp, Leq, Sp, Apply(mass, value));
        Formula totalMass = Seq(
            Sum, Underscore, Grp(Typed(value, pCarrier)), Sp,
            Apply(mass, value), Sp, Eq, Sp, D(1));
        Formula activeFactorization = Seq(
            Forall, Sp, Typed(context, Product(tupleS, hiddenType)), Comma, Sp,
            Apply(Call("marginal", contextLaw), context), Sp, Neq, Sp, D(0),
            Sp, Rightarrow, Sp, factorized);
        Formula smallerGain = Seq(
            Call("mutualInformation", lawSE), Sp, Minus, Sp,
            Call("mutualInformation", lawS));
        Formula largerGain = Seq(
            Call("mutualInformation", lawTE), Sp, Minus, Sp,
            Call("mutualInformation", lawT));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(indexType, type), Comma, Sp,
            Typed(hiddenType, type), Comma, RowBreak, Grp(),
            Typed(outputFamily, Arrow(indexType, type)), Comma, RowBreak, Grp(),
            Open, Call("Fintype", hiddenType), Sp, Land, Sp, finiteOutputs, Close,
            Sp, Rightarrow, RowBreak, Grp(),
            Forall, Sp, Typed(smaller, Call("Finset", indexType)), Comma, Sp,
            Typed(larger, Call("Finset", indexType)), Comma, Sp,
            Typed(added, indexType), Comma, RowBreak, Grp(),
            Typed(mass, Arrow(pCarrier, real)), Comma, RowBreak, Grp(),
            smaller, Sp, Subseteq, Sp, larger, Sp, Land, Sp,
            new Formula.Not(Seq(added, Sp, InMacro, Sp, larger)),
            Sp, Land, RowBreak, Grp(),
            Open, Open, nonnegative, Close, Sp, Land, Sp, totalMass, Close,
            Sp, Rightarrow, RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Sp,
            Define(lawS, lawCarrier(tupleS), selectedMarginal(smaller)), Comma,
            RowBreak, Grp(),
            Define(lawSE, lawCarrier(tupleSE), selectedMarginal(insertedSmaller)),
            Comma, RowBreak, Grp(),
            Define(lawT, lawCarrier(tupleT), selectedMarginal(larger)), Comma,
            RowBreak, Grp(),
            Define(lawTE, lawCarrier(tupleTE), mass), Comma, RowBreak, Grp(),
            Define(contextLaw, contextCarrier,
                Call("canonicalContextLaw", mass, smaller, larger, added)),
            RowBreak, Grp(),
            Operatorname, Grp(F.Id("in")), Sp,
            Open, activeFactorization, Close, Sp, Rightarrow, RowBreak, Grp(),
            smallerGain, Sp, Geq, Sp, largerGain, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
