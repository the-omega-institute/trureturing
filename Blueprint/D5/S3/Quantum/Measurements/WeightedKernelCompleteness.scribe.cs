using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class WeightedKernelCompletenessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strictly positive weighted effect quadratics have the common trace-effect kernel and are positive exactly under informational completeness.",
        H("Weighted Kernel Completeness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weighted-kernel-completeness"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Measurements/WeightedKernelCompleteness."
                        + "weighted_kernel_completeness"),
                H("Positive weights preserve the common effect kernel"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On the real traceless-Hermitian carrier, the weighted Gramian is the "
                            + "finite sum of the positive effect weights times squared trace-effect coordinates.")),
                    Paragraph(Text(
                        "Strict positivity forces its kernel to be exactly the intersection of "
                            + "the individual effect kernels. The quadratic form is positive "
                            + "definite precisely when the effect-coordinate readout is injective."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d");
        Formula index = F.Id("I");
        Formula i = F.Id("i");
        Formula effects = F.Id("e");
        Formula weight = F.Id("w");
        Formula observable = F.Id("D");
        Formula nat = Seq(Operatorname, Grp(F.Id("Nat")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula carrier = Call("traceZeroHermitian", d);
        Formula effectAt = Seq(effects, Underscore, Grp(i));
        Formula coordinate = Call("Tr", Seq(observable, Sp, effectAt));
        Formula gramian = Call("weightedGramian", effects, weight, observable);
        Formula kernel = Seq(OpenBrace, observable, Sp, Mid, Sp, gramian, Sp, Eq, Sp, FormulaDsl.D(0), CloseBrace);
        Formula intersection = Seq(OpenBrace, observable, Sp, Mid, Sp,
            Forall, Sp, Typed(i, index), Comma, Sp,
            coordinate, Sp, Eq, Sp, FormulaDsl.D(0), CloseBrace);
        Formula positive = Seq(Forall, Sp, Typed(observable, carrier), Comma, Sp,
            observable, Sp, Neq, Sp, FormulaDsl.D(0), Sp, Rightarrow, Sp,
            D(0), Sp, Lt, Sp, gramian);
        Formula signature = Seq(
            observable, Colon, Sp, carrier, Sp, Mapsto, Sp,
            Open, Typed(i, index), Sp, Mapsto, Sp, coordinate, Close);
        Formula injective = Call("Injective", signature);
        Formula positiveWeights = Seq(
            Forall, Sp, Typed(i, index), Comma, Sp,
            D(0), Sp, Lt, Sp, Call("w", i));
        return Disp(Seq(
            Forall, Sp, Typed(d, nat), Comma, Sp,
            Call("NeZero", d), Comma, Sp,
            Typed(index, type), Comma, Sp,
            Instance("Fintype", index), Comma, Sp,
            Typed(effects, Arrow(index, carrier)), Comma, Sp,
            Typed(weight, Arrow(index, reals)), Comma, Sp,
            positiveWeights, Sp, Rightarrow, Sp,
            kernel, Sp, Eq, Sp, intersection, Sp, Land, Sp,
            Seq(positive, Sp, Iff, Sp, injective), Dot));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Instance(string name, Formula value) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, value, Close, CloseBracket);
}
