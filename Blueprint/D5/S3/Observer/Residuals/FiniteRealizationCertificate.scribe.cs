using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Residuals;

internal sealed class FiniteRealizationCertificateDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Residuals/FiniteRealizationCertificate."
            + "finite_realization_certificate";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every unrealizable real protocol signature has a finite strict linear certificate.",
        H("Finite Realization Certificate"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-realization-certificate"),
            DeclarationHandle.Create(Declaration),
            H("Unrealizable signatures have finite linear witnesses"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A compact convex state set and its continuous affine real readouts "
                        + "construct the realization image through the canonical joint readout.")),
                Paragraph(Text(
                    "Strict separation produces a continuous linear functional on the product "
                        + "signature space. Continuity at zero forces that functional to depend "
                        + "on only finitely many protocol coordinates.")),
                Paragraph(Text(
                    "The displayed lower-completion coercions make the supremum equal negative "
                        + "infinity when the state set is empty. For every nonempty state set, "
                        + "they reduce to the ordinary attained real supremum."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("State");
        Formula protocol = F.Id("Protocol");
        Formula states = F.Id("X");
        Formula readout = F.Id("e");
        Formula signature = F.Id("y");
        Formula selected = F.Id("S");
        Formula coefficient = F.Id("c");
        Formula p = F.Id("p");
        Formula x = F.Id("x");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula stateSet = Call("Set", state);
        Formula affineReadout = Call("ContinuousAffineMap", real, state, real);
        Formula readoutType = Arrow(protocol, affineReadout);
        Formula signatureType = Arrow(protocol, real);
        Formula profile = F.Id("Sigma");
        Formula profileType = Arrow(state, signatureType);
        Formula profileConstruction = Call("jointReadout", readout);
        Formula realizableImage = Call("image", profile, states);
        Formula selectedType = Call("Finset", protocol);
        Formula formalValue = FiniteSum(
            p, selected,
            Seq(Call("apply", coefficient, p), Sp, Cdot, Sp,
                Call("apply", signature, p)));
        Formula realizedValue = FiniteSum(
            p, selected,
            Seq(Call("apply", coefficient, p), Sp, Cdot, Sp,
                Call("apply", readout, p, x)));
        Formula lowerSupremum = Seq(
            Operatorname, Grp(F.Id("supWithBot")), Underscore,
            Grp(x, Sp, InMacro, Sp, states), Sp,
            Call("withBotCoe", realizedValue));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp,
                Typed(Seq(state, Comma, Sp, protocol), type), Comma),
            Seq(
                Grp(), Typeclass("TopologicalSpace", state), Comma, Sp,
                Typeclass("AddCommGroup", state), Comma, Sp,
                Typeclass("Module", real, state), Comma),
            Seq(Forall, Sp, Typed(states, stateSet), Comma),
            Seq(
                Grp(), Call("IsCompact", states), Sp, Land, Sp,
                Call("Convex", real, states), Comma),
            Seq(
                Forall, Sp, Typed(readout, readoutType), Comma, Sp,
                Typed(signature, signatureType), Comma),
            Seq(
                Grp(), F.Id("let"), Sp, Typed(profile, profileType), Sp,
                Eq, Sp, profileConstruction, Semi),
            Seq(
                Neg, Sp, Open, signature, Sp, InMacro, Sp,
                realizableImage, Close, Sp, Rightarrow),
            Seq(
                Grp(), Exists, Sp, Typed(selected, selectedType), Comma, Sp,
                Exists, Sp, Typed(coefficient, signatureType), Comma),
            Seq(
                Grp(), Call("withBotCoe", formalValue), Sp, Gt, Sp,
                lowerSupremum, Dot),
        ]));
    }

    private static Formula FiniteSum(
        Formula index, Formula selected, Formula summand) =>
        Seq(
            Sum, Underscore,
            Grp(index, Sp, InMacro, Sp, selected), Sp,
            summand);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Typeclass(string name, params Formula[] arguments) =>
        Seq(OpenBracket, Call(name, arguments), CloseBracket);

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
