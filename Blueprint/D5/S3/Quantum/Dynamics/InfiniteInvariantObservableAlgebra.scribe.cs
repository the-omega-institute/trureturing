using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class InfiniteInvariantObservableAlgebraDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The supremum of the finite pullback chain is the least invariant observable algebra.",
        H("Infinite Invariant Observable Algebra"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("infinite-invariant-observable-algebra"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Dynamics/InfiniteInvariantObservableAlgebra."
                        + "infinite_invariant_observable_algebra"),
                H("The infinite pullback chain stabilizes canonically"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The infinite algebra is the supremum of the canonical finite pullback "
                            + "closures. Finite-system leastness places every finite stage below "
                            + "the least invariant extension, while the stable stage is itself "
                            + "one of the supremum members.")),
                    Paragraph(Text(
                        "The public clauses expose stabilization, current-readout containment, "
                            + "pullback invariance, leastness, and the canonical stable-state "
                            + "evaluation rule."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.Add(Seq(Comma, Sp));
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("Y");
        Formula output = F.Id("O");
        Formula update = F.Id("tau");
        Formula readout = F.Id("q");
        Formula depth = Call("predictionStabilityDepth", update, readout);
        Formula infinite = Call("infiniteKoopmanClosure", update, readout);
        Formula finite = Call("finiteKoopmanClosure", update, readout, depth);
        Formula evaluation = Call("stableObservableAlgebraEquiv", update, readout);
        Formula projection = Call("completionProjection", update, readout, F.Id("y"));

        return Disp(Seq(
            Forall, Sp, state, Comma, Sp, output, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, state, Close, CloseBracket,
            Comma, Sp, OpenBracket, Operatorname, Grp(F.Id("Nonempty")), Open, state,
            Close, CloseBracket, Comma, RowBreak, Grp(),
            update, Colon, Sp, F.Id("Y"), Sp, To, Sp, F.Id("Y"), Comma, Sp,
            readout, Colon, Sp, F.Id("Y"), Sp, To, Sp, output, Comma, Sp,
            Call("Surjective", readout), Comma, RowBreak, Grp(),
            infinite, Sp, Eq, Sp, finite, Sp, Land, Sp,
            Call("initialObservableAlgebra", readout), Sp, Le, Sp, infinite, Sp, Land, Sp,
            Call("PullbackInvariant", update, infinite), Sp, Land, Sp,
            infinite, Sp, Eq, Sp, Call("sInf", Call("invariantObservableExtensions", update, readout)),
            Sp, Land, Sp, Forall, Sp, F.Id("f"), InMacro, Sp, finite, Comma, Sp,
            F.Id("y"), InMacro, Sp, state, Comma, Sp,
            evaluation, Open, F.Id("f"), Close, Open, projection, Close,
            Sp, Eq, Sp, F.Id("f"), Open, F.Id("y"), Close, Dot));
    }
}
