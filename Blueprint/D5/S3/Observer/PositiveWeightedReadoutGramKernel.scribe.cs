using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer;

internal sealed class PositiveWeightedReadoutGramKernelDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/PositiveWeightedReadoutGramKernel."
            + "positive_weighted_readout_gram";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite positive-weighted readout Gram operator has the common readout kernel.",
        H("Positive Weighted Readout Gram Kernel"),
        Blocks(Describe.Lean(
            DescribeId.Create("positive-weighted-readout-gram-kernel"),
            DeclarationHandle.Create(Declaration),
            H("Strictly positive weights preserve exactly the common readout kernel"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The index type is finite, the state space is a finite-dimensional real "
                        + "inner-product space, and each readout may have its own finite-dimensional "
                        + "real inner-product codomain.")),
                Paragraph(Text(
                    "The energy identity follows from the adjoint pairing. If the Gram energy "
                        + "vanishes, nonnegativity of every summand and strict positivity of every "
                        + "weight force each readout norm to vanish.")),
                Paragraph(Text(
                    "The empty protocol family is included: both kernels are then the whole state "
                        + "space. Strict positivity is essential for nonempty families because a "
                        + "zero weight could hide a nonzero readout."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula index = F.Id("I");
        Formula i = F.Id("i");
        Formula state = F.Id("V");
        Formula output = new Formula.Subscript(F.Id("Y"), i);
        Formula readout = F.Id("C");
        Formula readoutAt = new Formula.Subscript(readout, i);
        Formula weight = F.Id("w");
        Formula weightAt = new Formula.Subscript(weight, i);
        Formula vector = F.Id("v");
        Formula gram = F.Id("W");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula readoutValue = Apply(readoutAt, vector);
        Formula gramTerm = Seq(
            weightAt, Sp, readoutAt, Caret, Grp(Star), Sp, readoutAt);
        Formula readoutFamilyType = Seq(
            Forall, Sp, Typed(i, index), Comma, Sp, Arrow(state, output));
        Formula gramDefinition = Seq(
            gram, Sp, Colon, Eq, Sp, Sum, Underscore,
            Grp(i, Sp, InMacro, Sp, index), Sp, gramTerm);
        Formula energy = Seq(
            Langle, Sp, vector, Comma, Sp, gram, vector, Rangle, Sp, Eq, Sp,
            Sum, Underscore, Grp(i, Sp, InMacro, Sp, index), Sp,
            weightAt, Sp, Call("norm", readoutValue), Caret, Grp(D(2)));
        Formula commonKernel = Seq(
            OpenBrace, vector, Sp, InMacro, Sp, state, Sp, Mid, Sp,
            Forall, Sp, Typed(i, index), Comma, Sp,
            readoutValue, Sp, Eq, Sp, D(0), CloseBrace);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(index, type), Comma, Sp,
                Instance("Fintype", index), Comma),
            Seq(
                Grp(), Typed(state, type), Comma, Sp,
                Call("RealInnerFD", state), Comma),
            Seq(
                Grp(), Forall, Sp, Typed(i, index), Comma, Sp,
                Typed(output, type), Sp, Land, Sp,
                Call("RealInnerFD", output), Comma),
            Seq(
                Grp(), Typed(readout, readoutFamilyType), Comma, Sp,
                Typed(weight, Arrow(index, reals)), Comma),
            Seq(
                Grp(), Forall, Sp, Typed(i, index), Comma, Sp,
                D(0), Sp, Lt, Sp, weightAt, Comma),
            Seq(Grp(), gramDefinition, Comma),
            Seq(
                Grp(), Forall, Sp, Typed(vector, state), Comma, Sp,
                energy, Comma),
            Seq(
                Grp(), Call("ker", gram), Sp, Eq, Sp,
                commonKernel, Dot),
        ]));
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Instance(string name, Formula value) =>
        Seq(OpenBracket, Call(name, value), CloseBracket);

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
