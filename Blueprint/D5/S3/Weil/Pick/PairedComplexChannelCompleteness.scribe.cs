using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Pick;

internal sealed class PairedComplexChannelCompletenessDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strictly positive paired complex-channel energies have the common channel kernel "
            + "and are definite exactly when the joint observation is injective.",
        H("Paired Complex-Channel Completeness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("paired-complex-channel-completeness"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Pick/PairedComplexChannelCompleteness."
                        + "paired_complex_channel_completeness"),
                H("Positive paired channels preserve the common kernel"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The energy is the finite sum of positive sensor weights times the "
                            + "two complex readout norm squares. Therefore zero total energy "
                            + "forces both channels to vanish at every sensor.")),
                    Paragraph(Text(
                        "The same kernel identity converts strict positivity on every nonzero "
                            + "state into injectivity of the paired observation map, and conversely. "
                            + "No finite-dimensional premise on the state space is required."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < args.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(args[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Apply(Formula function, params Formula[] args)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < args.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(args[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula carrier = F.Id("V");
        Formula index = F.Id("I");
        Formula i = F.Id("i");
        Formula x = F.Id("x");
        Formula minus = F.Id("m");
        Formula plus = F.Id("p");
        Formula weight = F.Id("w");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula linearReadout = Call("LinearMap", carrier, complex);
        Formula readoutFamily = Arrow(index, linearReadout);
        Formula energy = Call(
            "pairedComplexChannelEnergy", minus, plus, weight, x);
        Formula kernel = Seq(
            OpenBrace, x, Sp, Mid, Sp, energy, Sp, Eq, Sp, D(0), CloseBrace);
        Formula commonKernel = Seq(
            OpenBrace, x, Sp, Mid, Sp,
            Forall, Sp, Typed(i, index), Comma, Sp,
            Apply(Seq(minus, Underscore, Grp(i)), x), Sp, Eq, Sp, D(0),
            Sp, Land, Sp,
            Apply(Seq(plus, Underscore, Grp(i)), x), Sp, Eq, Sp, D(0),
            CloseBrace);
        Formula strictPositive = Seq(
            Forall, Sp, Typed(x, carrier), Comma, Sp,
            x, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
            D(0), Sp, Lt, Sp, energy);
        Formula injective = Call(
            "Injective", Call("pairedComplexObservation", minus, plus));
        Formula positiveWeights = Seq(
            Forall, Sp, Typed(i, index), Comma, Sp,
            D(0), Sp, Lt, Sp, Apply(weight, i));

        return Disp(Seq(
            Forall, Sp, Typed(carrier, type), Comma, Sp,
            Instance("AddCommGroup", carrier), Comma, Sp,
            Instance("Module", complex, carrier), Comma, Sp,
            Typed(index, type), Comma, Sp,
            Instance("Fintype", index), Comma, Sp,
            Typed(minus, readoutFamily), Comma, Sp,
            Typed(plus, readoutFamily), Comma, Sp,
            Typed(weight, Arrow(index, reals)), Comma, Sp,
            positiveWeights, Sp, Rightarrow, Sp,
            kernel, Sp, Eq, Sp, commonKernel, Sp, Land, Sp,
            Open, strictPositive, Close, Sp, Iff, Sp, injective, Dot));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Instance(string name, params Formula[] args)
    {
        var items = new List<Formula> {
            OpenBracket, Operatorname, Grp(F.Id(name)), Open
        };
        for (var index = 0; index < args.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(args[index]);
        }

        items.AddRange([Close, CloseBracket]);
        return Seq([.. items]);
    }
}
