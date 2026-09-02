using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class OneObserverOperatorNonreconstructionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Linear/OneObserverOperatorNonreconstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One squared operator reading is reflection-invariant and cannot reconstruct direction.",
        H("One-Observer Operator Non-Reconstruction"),
        Blocks(Describe.Lean(
            DescribeId.Create("one-observer-operator-nonreconstruction"),
            DeclarationHandle.Create(Prefix + "one_observer_operator_nonreconstruction"),
            H("One observer cannot reconstruct operator direction"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let V be a nontrivial real normed vector space. For a linear endomorphism "
                        + "H and observer position t, the reading is constructed as "
                        + "observerSquare(H,t) = (H - t id)^2 on the same operator carrier.")),
                Paragraph(Text(
                    "No function of that single reading recovers every H. Reflection across t "
                        + "replaces H by 2t id - H and leaves the reading unchanged, giving the "
                        + "explicit ambiguity behind the non-reconstruction clause.")),
                Paragraph(Text(
                    "If D is the strong pointwise derivative of the operator bundle at t, "
                        + "derivative uniqueness gives D = 2(t id - H) and hence recovers H. "
                        + "For every nonzero free offset h, the displayed two-position formula "
                        + "likewise reconstructs H from the readings at t and t+h.")),
                Paragraph(Text(
                    "Repository, pinned Mathlib, and installed third-party package searches "
                        + "found no exact packaged theorem. The proof uses the endomorphism ring, "
                        + "pointwise polynomial differentiation, and derivative uniqueness."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("V");
        Formula observer = F.Id("t");
        Formula offset = F.Id("h");
        Formula source = F.Id("H");
        Formula derivative = F.Id("D");
        Formula point = F.Id("x");
        Formula variable = F.Id("s");
        Formula reconstruct = F.Id("reconstruct");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula endomorphism = Call("ModuleEnd", real, state);
        Formula identity = Call("id", state);
        Formula two = D(2);
        Formula zero = D(0);
        Formula half = Seq(Frac, Grp(D(1)), Grp(two));

        Formula Reading(Formula map, Formula position) =>
            Call("observerSquare", map, position);
        Formula Apply(Formula map, Formula argument) =>
            Seq(map, Open, argument, Close);
        Formula Scale(Formula scalar, Formula map) =>
            Seq(scalar, Sp, map);
        Formula ShiftedIdentity(Formula position) => Scale(position, identity);

        Formula reflected = Seq(
            Scale(Seq(two, Sp, observer), identity), Sp, Minus, Sp, source);
        Formula noReconstruction = Seq(
            Neg, Sp, Exists, Sp,
            Typed(reconstruct, Seq(endomorphism, Sp, Rightarrow, Sp, endomorphism)),
            Comma, Sp, Forall, Sp, Typed(source, endomorphism), Comma, Sp,
            Apply(reconstruct, Reading(source, observer)), Sp, Eq, Sp, source);
        Formula reflectionClause = Seq(
            Forall, Sp, Typed(source, endomorphism), Comma, Sp,
            Reading(reflected, observer), Sp, Eq, Sp, Reading(source, observer));

        Formula curve = Seq(
            Open, Typed(variable, real), Sp, Mapsto, Sp,
            Apply(Reading(source, variable), point), Close);
        Formula derivativePremise = Seq(
            Forall, Sp, Typed(point, state), Comma, Sp,
            Call("HasDerivAt", curve, Apply(derivative, point), observer));
        Formula derivativeValue = Seq(
            derivative, Sp, Eq, Sp, Scale(two, Grp(
                ShiftedIdentity(observer), Sp, Minus, Sp, source)));
        Formula derivativeRecovery = Seq(
            ShiftedIdentity(observer), Sp, Minus, Sp, Scale(half, derivative),
            Sp, Eq, Sp, source);
        Formula derivativeClause = Seq(
            Forall, Sp, Typed(source, endomorphism), Comma, Sp,
            Typed(derivative, endomorphism), Comma, Sp,
            Open, derivativePremise, Close, Sp, Rightarrow, Sp,
            Open, derivativeValue, Sp, Land, Sp, derivativeRecovery, Close);

        Formula offsetSquare = Seq(offset, Caret, Grp(two));
        Formula secondNumerator = Seq(
            Reading(source, observer), Sp, Minus, Sp,
            Reading(source, Seq(observer, Sp, Plus, Sp, offset)), Sp, Plus, Sp,
            Scale(offsetSquare, identity));
        Formula secondRecovery = Seq(
            ShiftedIdentity(observer), Sp, Plus, Sp,
            Scale(Seq(Frac, Grp(D(1)), Grp(two, Sp, offset)),
                Grp(secondNumerator)),
            Sp, Eq, Sp, source);
        Formula secondObserverClause = Seq(
            Forall, Sp, Typed(source, endomorphism), Comma, Sp,
            Typed(offset, real), Comma, Sp,
            offset, Sp, Neq, Sp, zero, Sp, Rightarrow, Sp, secondRecovery);

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Typed(state, type), Comma),
            Seq(Grp(), Typeclass("NormedAddCommGroup", state), Sp, Land, Sp,
                Typeclass("NormedSpace", real, state), Sp, Land, Sp,
                Typeclass("Nontrivial", state), Sp, Rightarrow),
            Seq(Grp(), Forall, Sp, Typed(observer, real), Comma),
            Seq(Grp(), Open, noReconstruction, Close, Sp, Land),
            Seq(Grp(), Open, reflectionClause, Close, Sp, Land),
            Seq(Grp(), Open, derivativeClause, Close, Sp, Land),
            Seq(Grp(), Open, secondObserverClause, Close, Dot)
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
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}
