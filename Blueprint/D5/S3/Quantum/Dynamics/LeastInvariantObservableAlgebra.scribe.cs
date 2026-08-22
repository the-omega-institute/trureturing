using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class LeastInvariantObservableAlgebraDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounded readout pullbacks reach the least invariant observable algebra at the least stable depth.",
        H("Least Invariant Observable Algebra"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("least-invariant-observable-algebra"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Dynamics/LeastInvariantObservableAlgebra."
                        + "least_invariant_observable_algebra"),
                H("Finite pullbacks reach the least invariant algebra"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The current observable algebra is the range of complex-function pullback "
                            + "along the surjective readout. The depth algebra is constructed by "
                            + "adjoining its pullbacks through update times at most that depth.")),
                    Paragraph(Text(
                        "The first two public clauses state monotonicity of the entire finite chain "
                            + "and equality of consecutive stages at the source's least prediction-"
                            + "stable depth. The third states closure under one further pullback.")),
                    Paragraph(Text(
                        "The fourth clause identifies the stable stage with the infimum of every "
                            + "unital star subalgebra containing the current readout algebra and "
                            + "closed under pullback. The final clause exposes the named canonical "
                            + "equivalence to functions on complete prediction states and gives its "
                            + "value on every projected representative.")),
                    Paragraph(Text(
                        "The proof applies the frozen full-closure theorem, permanent partition "
                            + "stability, and stabilized quotient equivalence directly."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Indexed(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("Y");
        Formula output = F.Id("O");
        Formula update = Tau;
        Formula readout = F.Id("q");
        Formula depth = Indexed(F.Id("m"), Star);
        Formula first = F.Id("i");
        Formula second = F.Id("j");
        Formula function = F.Id("f");
        Formula point = F.Id("y");
        Formula algebraAt(Formula index) =>
            Call("finiteKoopmanClosure", update, readout, index);
        Formula stableAlgebra = algebraAt(depth);
        Formula nextAlgebra = algebraAt(Seq(depth, Sp, Plus, Sp, D(1)));
        Formula extensions = Call("invariantObservableExtensions", update, readout);
        Formula projection = Call("completionProjection", update, readout, point);
        Formula equivalence = Call("stableObservableAlgebraEquiv", update, readout);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, output, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, state, Close,
            CloseBracket, Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Nonempty")), Open, state, Close,
            CloseBracket, Comma, RowBreak, Grp(),
            update, Colon, Sp, Arrow(state, state), Comma, Sp,
            readout, Colon, Sp, Arrow(state, output), Comma, Sp,
            Call("Surjective", readout), Comma, RowBreak, Grp(),
            depth, Sp, Colon, Eq, Sp,
            Call("predictionStabilityDepth", update, readout), Comma, RowBreak, Grp(),
            Open, Forall, Sp, first, Comma, Sp, second, InMacro, Sp,
            Mathbb, Grp(F.Id("N")), Comma, Sp, first, Sp, Le, Sp, second,
            Sp, Rightarrow, Sp, algebraAt(first), Sp, Le, Sp, algebraAt(second), Close,
            Sp, Land, RowBreak, Grp(),
            stableAlgebra, Sp, Eq, Sp, nextAlgebra,
            Sp, Land, RowBreak, Grp(),
            Call("PullbackInvariant", update, stableAlgebra),
            Sp, Land, RowBreak, Grp(),
            stableAlgebra, Sp, Eq, Sp, Call("sInf", extensions),
            Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, function, InMacro, Sp, stableAlgebra, Comma, Sp,
            point, InMacro, Sp, state, Comma, Sp,
            equivalence, Open, function, Close, Open, projection, Close,
            Sp, Eq, Sp, function, Open, point, Close, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
