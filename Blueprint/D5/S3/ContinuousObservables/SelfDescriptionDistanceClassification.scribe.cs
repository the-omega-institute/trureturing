using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ContinuousObservables;

internal sealed class SelfDescriptionDistanceClassificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Self-description differences split into zero, finite-reachable, and horizon distances.",
        H("Self-Description Distance Classification"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("self-description-distance-classification"),
                DeclarationHandle.Create(
                    "D5/S3/ContinuousObservables/SelfDescriptionDistanceClassification."
                        + "self_description_distance_classification"),
                H("Self-description differences have three operational distance classes"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A self-description difference is an endpoint pair separated by at "
                            + "least one member of the supplied self-readout family. The outside "
                            + "distance is the canonical supremum over bounded unit-edge readouts "
                            + "for the supplied permutation update.")),
                    Paragraph(Text(
                        "Zero distance forces every admissible readout to agree. Infinite "
                            + "distance excludes every finite signed update path. If all "
                            + "self-description differences are in one of those two hidden "
                            + "classes, no admissible readout can distinguish a pair along such "
                            + "a path.")),
                    Paragraph(Text(
                        "A finite-positive distance supplies both an admissible separating "
                            + "readout and a signed update path. The imported permutation-horizon "
                            + "theorem bounds the observer distance by that path's length."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        Formula state = F.Id("I");
        Formula selfCarrier = F.Id("S");
        Formula update = F.Id("tau");
        Formula selfReadout = F.Id("Delta");
        Formula pair = F.Id("p");
        Formula self = F.Id("s");
        Formula observable = F.Id("f");
        Formula exponent = F.Id("n");
        Formula pairType = Seq(state, Sp, Times, Sp, state);
        Formula first = Call("fst", pair);
        Formula second = Call("snd", pair);
        Formula differenceCarrier = F.Id("D");
        Formula differenceSet = new Formula.SetBuilder(
            Seq(
                Exists, Sp, Typed(self, selfCarrier), Comma, Sp,
                Call("selfReadout", selfReadout, self, first), Sp, Neq, Sp,
                Call("selfReadout", selfReadout, self, second)),
            pair,
            pairType);
        Formula distance = Call("observerDistance", update, first, second);
        Formula agreement = Agreement(update, state, real, observable, first, second);
        Formula noPath = NoPath(update, state, integers, exponent, first, second);
        Formula finiteClass = Seq(D(0), Sp, Lt, Sp, distance, Sp, Lt, Sp, Infty);
        Formula zeroClass = Seq(
            distance, Sp, Eq, Sp, D(0), Sp, Land, Sp, agreement);
        Formula topClass = Seq(
            distance, Sp, Eq, Sp, Infty, Sp, Land, Sp, noPath);
        Formula trichotomy = Seq(
            Forall, Sp, pair, Sp, InMacro, Sp, differenceCarrier, Comma, Sp,
            Open, Open, zeroClass, Close, Sp, Lor, Sp,
            Open, finiteClass, Close, Sp, Lor, Sp,
            Open, topClass, Close, Close);
        Formula allHidden = Seq(
            Forall, Sp, pair, Sp, InMacro, Sp, differenceCarrier, Comma, Sp,
            Open, distance, Sp, Eq, Sp, D(0), Sp, Lor, Sp,
            distance, Sp, Eq, Sp, Infty, Close);
        Formula finiteBookkeeping = FiniteBookkeeping(
            update, state, real, integers, observable, exponent,
            first, second, distance, includeBound: false);
        Formula boundedFiniteBookkeeping = FiniteBookkeeping(
            update, state, real, integers, observable, exponent,
            first, second, distance, includeBound: true);
        Formula hiddenConsequence = Seq(
            Open, allHidden, Close, Sp, Rightarrow, Sp,
            Forall, Sp, pair, Sp, InMacro, Sp, differenceCarrier, Comma, Sp,
            Neg, Open, finiteBookkeeping, Close);
        Formula finiteConsequence = Seq(
            Forall, Sp, pair, Sp, InMacro, Sp, differenceCarrier, Comma, Sp,
            Open, finiteClass, Close, Sp, Rightarrow, Sp,
            boundedFiniteBookkeeping);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp,
                Typed(Seq(state, Comma, Sp, selfCarrier), type), Comma, Sp,
                Typed(update, Call("Perm", state)), Comma),
            Seq(
                Grp(), Typed(selfReadout,
                    Arrow(selfCarrier, Arrow(state, real))), Comma, Sp,
                Operatorname, Grp(F.Id("let")), Sp,
                differenceCarrier, Sp, Eq, Sp, differenceSet),
            Seq(
                Grp(), Operatorname, Grp(F.Id("in")), Sp,
                Open, trichotomy, Close, Sp, Land),
            Seq(Grp(), Open, hiddenConsequence, Close, Sp, Land),
            Seq(Grp(), Open, finiteConsequence, Close, Dot),
        ]));
    }

    private static Formula Agreement(
        Formula update,
        Formula state,
        Formula real,
        Formula observable,
        Formula first,
        Formula second) =>
        Seq(
            Forall, Sp, Typed(observable, Arrow(state, real)), Comma, Sp,
            Call("edgeAdmissible", update, observable), Sp, Rightarrow, Sp,
            Apply(observable, first), Sp, Eq, Sp, Apply(observable, second));

    private static Formula NoPath(
        Formula update,
        Formula state,
        Formula integers,
        Formula exponent,
        Formula first,
        Formula second)
    {
        Formula iterate = new Formula.Power(update, exponent);
        return Seq(
            Forall, Sp, Typed(exponent, integers), Comma, Sp,
            second, Sp, Neq, Sp, Apply(iterate, first));
    }

    private static Formula FiniteBookkeeping(
        Formula update,
        Formula state,
        Formula real,
        Formula integers,
        Formula observable,
        Formula exponent,
        Formula first,
        Formula second,
        Formula distance,
        bool includeBound)
    {
        Formula iterate = new Formula.Power(update, exponent);
        Formula body = Seq(
            Call("edgeAdmissible", update, observable), Sp, Land, Sp,
            Apply(observable, first), Sp, Neq, Sp, Apply(observable, second),
            Sp, Land, Sp,
            second, Sp, Eq, Sp, Apply(iterate, first));
        if (includeBound)
        {
            body = Seq(
                body, Sp, Land, Sp,
                distance, Sp, Leq, Sp, new Formula.Absolute(exponent));
        }

        return Seq(
            Exists, Sp, Typed(observable, Arrow(state, real)), Comma, Sp,
            Typed(exponent, integers), Comma, Sp, body);
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
