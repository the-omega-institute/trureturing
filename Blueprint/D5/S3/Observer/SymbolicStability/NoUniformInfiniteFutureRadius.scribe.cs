using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.SymbolicStability;

internal sealed class NoUniformInfiniteFutureRadiusDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden mechanical readouts have finite local stability but no uniform infinite-future radius.",
        H("No Uniform Infinite-Future Stability Radius"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("dense-boundaries-defeat-infinite-future-stability"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/SymbolicStability/NoUniformInfiniteFutureRadius."
                        + "no_uniform_infinite_future_stability_radius"),
                H("Boundary-driven prediction escape under an isometric circle update"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The theorem uses the literal golden slope phi^-2 and the integer "
                            + "floor-difference readout from the source construction. Its "
                            + "boundary set is the integer-lifted union of the first N + 1 "
                            + "cuts, and its update is addition by the same slope on the unit "
                            + "circle.")),
                    Paragraph(Text(
                        "Every real phase has arbitrarily close phases whose integer readouts "
                            + "separate at some future coordinate. Consequently no positive "
                            + "radius stabilizes the entire future, while every finite prefix "
                            + "has a positive common radius away from its lifted boundary set.")),
                    Paragraph(Text(
                        "The off-boundary condition is essential: finite-prefix stability is "
                            + "not asserted at a cut. Every iterate of the circle update "
                            + "preserves the initial distance exactly, and the final witnesses "
                            + "combine readout escape with that distance invariance."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula Indexed(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Applied(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Power(Formula function, Formula exponent) =>
        Seq(function, Caret, Grp(exponent));

    private static Formula SymbolAt(Formula readout, Formula index, Formula point) =>
        Applied(Indexed(readout, index), point);

    private static Formula TheoremFormula()
    {
        Formula readout = F.Id("w");
        Formula update = F.Id("R");
        Formula n = F.Id("n");
        Formula finite = F.Id("N");
        Formula thetaPrime = Seq(Theta, Apos);
        Formula distance = Call("d", thetaPrime, Theta);
        Formula split = Seq(
            SymbolAt(readout, n, thetaPrime), Sp, Neq, Sp,
            SymbolAt(readout, n, Theta));
        Formula closeSplit = Seq(
            Forall, Sp, Theta, Comma, Sp, Varepsilon, Gt, D(0), Comma, Sp,
            Exists, Sp, thetaPrime, Comma, Sp, n, Comma, Sp,
            distance, Sp, Lt, Sp, Varepsilon, Sp, Land, Sp, split);
        Formula finiteStability = Seq(
            Forall, Sp, finite, Comma, Sp, Theta, Comma, Sp,
            Neg, Sp, Call("goldenObserverPrefixBoundary", finite, Theta), Sp,
            Rightarrow, Sp, Exists, Sp, Varepsilon, Gt, D(0), Comma, Sp,
            Forall, Sp, thetaPrime, Comma, Sp, distance, Sp, Lt, Sp, Varepsilon, Sp,
            Rightarrow, Sp, Forall, Sp, n, Lt, finite, Comma, Sp,
            SymbolAt(readout, n, thetaPrime), Sp, Eq, Sp,
            SymbolAt(readout, n, Theta));
        Formula noRadius = Seq(
            Forall, Sp, Theta, Comma, Sp, Neg, Sp,
            Exists, Sp, Varepsilon, Gt, D(0), Comma, Sp,
            Forall, Sp, thetaPrime, Comma, Sp, distance, Sp, Lt, Sp, Varepsilon, Sp,
            Rightarrow, Sp, Forall, Sp, n, Comma, Sp,
            SymbolAt(readout, n, thetaPrime), Sp, Eq, Sp,
            SymbolAt(readout, n, Theta));
        Formula iterateDistance = Seq(
            Call("d", Applied(Power(update, n), thetaPrime), Applied(Power(update, n), Theta)),
            Sp, Eq, Sp, distance);
        Formula iterate = Seq(
            Forall, Sp, n, Comma, Sp, Theta, Comma, Sp, thetaPrime, Comma, Sp,
            iterateDistance);
        Formula interfaceEscape = Seq(
            Forall, Sp, Theta, Comma, Sp, Varepsilon, Gt, D(0), Comma, Sp,
            Exists, Sp, thetaPrime, Comma, Sp, n, Comma, Sp,
            distance, Sp, Lt, Sp, Varepsilon, Sp, Land, Sp, split, Sp, Land, Sp,
            iterateDistance);

        return Disp(Seq(
            Open, closeSplit, Close, Sp, Land, RowBreak,
            Open, finiteStability, Close, Sp, Land, RowBreak,
            Open, noRadius, Close, Sp, Land, RowBreak,
            Open, iterate, Close, Sp, Land, RowBreak,
            Open, interfaceEscape, Close, Dot));
    }
}
