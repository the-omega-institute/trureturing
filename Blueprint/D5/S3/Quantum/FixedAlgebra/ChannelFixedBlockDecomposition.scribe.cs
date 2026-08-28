using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FixedAlgebra;

internal sealed class ChannelFixedBlockDecompositionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/FixedAlgebra/ChannelFixedBlockDecomposition."
            + "channel_fixed_block_decomposition";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A record channel fixes exactly the full matrix blocks on its record classes.",
        H("Channel Fixed-Block Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("channel-fixed-block-decomposition"),
                DeclarationHandle.Create(Declaration),
                H("Channel fixed-block decomposition"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let d and e be natural dimensions and Lambda a finite decidable record-"
                            + "class type. The environment record is a complex amplitude table, "
                            + "and classOf assigns each address to its record class.")),
                    Paragraph(Text(
                        "The public classification premise identifies Gram entry one exactly "
                            + "with equality of record classes. The channel and Gram matrix are "
                            + "the canonical primitives imported from the record family.")),
                    Paragraph(Text(
                        "The class-supported algebra is defined directly by vanishing of entries "
                            + "between different classes. It is not defined as the range of the "
                            + "block map or as the channel fixed set.")),
                    Paragraph(Text(
                        "The named classifiedBlockAlgEquiv first embeds one full matrix algebra "
                            + "per proof-relevant class fiber and then applies the canonical sigma-"
                            + "fiber reindexing. The second displayed clause pins this equivalence "
                            + "to the original within-class matrix entries."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d");
        Formula e = F.Id("e");
        Formula classes = F.Id("Lambda");
        Formula record = F.Id("record");
        Formula classOf = F.Id("classOf");
        Formula address = F.Id("i");
        Formula secondAddress = F.Id("j");
        Formula alpha = F.Id("alpha");
        Formula rho = Rho;
        Formula blocks = F.Id("blocks");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula complexes = Seq(Mathbb, Grp(F.Id("C")));
        Formula finD = Call("Fin", d);
        Formula finE = Call("Fin", e);
        Formula matrixD = Call("Matrix", finD, finD, complexes);
        Formula fiber = new Formula.SetBuilder(
            Equal(Apply(classOf, address), alpha), address, finD);
        Formula blockMatrix = Call("Matrix", fiber, fiber, complexes);
        Formula blockProduct = Seq(
            Prod, Underscore, Grp(Typed(alpha, classes)), Sp, blockMatrix);
        Formula classAgreement = Seq(
            Forall, Sp, Typed(Seq(address, Comma, Sp, secondAddress), finD), Comma, Sp,
            Call("recordGram", record, address, secondAddress), Sp, Eq, Sp, D(1),
            Sp, Iff, Sp,
            Apply(classOf, address), Sp, Eq, Sp, Apply(classOf, secondAddress));
        Formula support = Seq(
            Forall, Sp, Typed(Seq(address, Comma, Sp, secondAddress), finD), Comma, Sp,
            Apply(classOf, address), Sp, Neq, Sp, Apply(classOf, secondAddress),
            Sp, Rightarrow, Sp, Entry(rho, address, secondAddress), Sp, Eq, Sp, D(0));
        Formula fixedCharacterization = Seq(
            Forall, Sp, Typed(rho, matrixD), Comma, Sp,
            Call("recordChannel", record, rho), Sp, Eq, Sp, rho,
            Sp, Iff, Sp, support);
        Formula equivalenceValue = Apply(
            Call("classifiedBlockAlgEquiv", classOf), blocks);
        Formula blockComputation = Seq(
            Forall, Sp, Typed(blocks, blockProduct), Comma, Sp,
            Typed(alpha, classes), Comma, Sp,
            Typed(Seq(address, Comma, Sp, secondAddress), fiber), Comma, Sp,
            Entry(equivalenceValue, address, secondAddress), Sp, Eq, Sp,
            Entry(Apply(blocks, alpha), address, secondAddress));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(Seq(d, Comma, Sp, e), naturals), Comma, Sp,
                Typed(classes, TypeUniverse()), Comma, Sp,
                OpenBracket, Call("Fintype", classes), CloseBracket, Comma, Sp,
                OpenBracket, Call("DecidableEq", classes), CloseBracket, Comma),
            Seq(
                Forall, Sp,
                Typed(record, Arrow(finD, Arrow(finE, complexes))), Comma, Sp,
                Typed(classOf, Arrow(finD, classes)), Comma),
            Seq(
                Open, classAgreement, Close, Sp, Rightarrow, Sp),
            Seq(
                Open, fixedCharacterization, Close, Sp, Land),
            Seq(
                Open, blockComputation, Close, Dot),
        ]));
    }

    private static Formula Entry(Formula matrix, Formula i, Formula j) =>
        Call("entry", matrix, i, j);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

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
