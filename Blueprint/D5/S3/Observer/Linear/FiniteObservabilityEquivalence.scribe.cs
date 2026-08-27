using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class FiniteObservabilityEquivalenceDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite readout residual, full rank, and Gram positivity are equivalent.",
        H("Finite Observability Equivalence"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-observability-equivalence"),
            DeclarationHandle.Create(
                "D5/S3/Observer/Linear/FiniteObservabilityEquivalence."
                    + "finite_observability_equivalence"),
            H("Kernel, rank, and Gram criteria agree"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The stacked readout is constructed from every iterate before the finite "
                    + "horizon. Its residual is its kernel and its Gram operator is the "
                    + "adjoint composed with the stacked readout. Rank-nullity and the "
                    + "Gram energy identity make all three public criteria equivalent."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("V");
        Formula output = F.Id("Y");
        Formula update = F.Id("T");
        Formula readout = F.Id("C");
        Formula horizon = F.Id("n");
        Formula time = F.Id("t");
        Formula vector = F.Id("x");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula observability = new Formula.Subscript(F.Id("O"), horizon);
        Formula residual = new Formula.Subscript(F.Id("N"), horizon);
        Formula gram = new Formula.Subscript(F.Id("W"), horizon);
        Formula finHorizon = Call("Fin", horizon);
        Formula stackedSpace = Call(
            "PiLp", D(2), Seq(finHorizon, Sp, To, Sp, output));
        Formula updateType = Call("LinearMap", real, state, state);
        Formula readoutType = Call("LinearMap", real, state, output);
        Formula observabilityType = Call("LinearMap", real, state, stackedSpace);
        Formula observedAtTime = Seq(
            readout, Open, update, Caret, Grp(time), Sp, vector, Close);
        Formula stackedReadout = Seq(
            Open, observedAtTime, Close, Underscore,
            Grp(time, Colon, Sp, finHorizon));
        Formula zeroSubspace = Seq(OpenBrace, D(0), CloseBrace);
        Formula zeroResidual = Seq(residual, Sp, Eq, Sp, zeroSubspace);
        Formula fullRank = Seq(
            Call("finrank", real, Call("range", observability)), Sp, Eq, Sp,
            Call("finrank", real, state));
        Formula gramPositive = Seq(
            Forall, Sp, Typed(vector, state), Comma, Sp,
            vector, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp, D(0), Sp, Lt, Sp,
            Langle, Sp, vector, Comma, Sp, gram, Sp, vector, Sp, Rangle,
            Underscore, Grp(real));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(Seq(state, Comma, Sp, output), type), Comma),
            Seq(
                Grp(), Typeclass("NormedAddCommGroup", state), Comma, Sp,
                Typeclass("InnerProductSpace", real, state), Comma, Sp,
                Typeclass("FiniteDimensional", real, state), Comma),
            Seq(
                Grp(), Typeclass("NormedAddCommGroup", output), Comma, Sp,
                Typeclass("InnerProductSpace", real, output), Comma, Sp,
                Typeclass("FiniteDimensional", real, output), Comma),
            Seq(
                Forall, Sp, Typed(update, updateType), Comma, Sp,
                Typed(readout, readoutType), Comma, Sp,
                Typed(horizon, natural), Comma),
            Seq(
                Grp(), F.Id("let"), Sp, Typed(observability, observabilityType),
                Comma, Sp, observability, Open, vector, Close, Sp, Eq, Sp,
                stackedReadout, Semi),
            Seq(
                Grp(), F.Id("let"), Sp, residual, Sp, Eq, Sp,
                Call("ker", observability), Semi, Sp,
                F.Id("let"), Sp, gram, Sp, Eq, Sp,
                observability, Caret, Grp(Star), Sp, observability, Semi),
            Seq(
                Grp(), zeroResidual, Sp, Iff, Sp,
                fullRank, Sp, Iff, Sp,
                gramPositive, Dot),
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
