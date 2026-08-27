using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FixedAlgebra;

internal sealed class RecordChannelFixedPointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A record channel fixes exactly the matrices satisfying its entrywise Gram equations.",
        H("Record Channel Fixed Point"),
        Blocks(Describe.Lean(
            DescribeId.Create("record-channel-fixed-iff-entry-equations"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/FixedAlgebra/RecordChannelFixedPoint."
                    + "record_channel_fixed_iff_entry_equations"),
            H("Record-channel fixed points are entrywise Gram equations"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The record Gram matrix and channel are the canonical source-constructed "
                    + "primitives. Comparing matrix entries turns channel equality into "
                    + "the displayed product equation, and the converse reconstructs the "
                    + "channel entry by entry."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d");
        Formula e = F.Id("e");
        Formula record = F.Id("record");
        Formula rho = F.Id("rho");
        Formula index = F.Id("i");
        Formula indexPrime = F.Id("j");
        Formula complex = F.Id("Complex");
        Formula fin = F.Id("Fin");
        Formula matrix = F.Id("Matrix");
        Formula recordType = Arrow(fin, Arrow(fin, complex));
        Formula matrixType = Apply(matrix, Apply(fin, d), Apply(fin, d), complex);
        Formula gram = Apply(F.Id("recordGram"), record, index, indexPrime);
        Formula entry = Apply(Apply(rho, index), indexPrime);
        Formula fixedPoint = Seq(Apply(F.Id("recordChannel"), record, rho), Sp, Eq, Sp, rho);
        Formula equations = Seq(
            Forall, Sp, index, Comma, Sp, indexPrime, Colon, Sp, Apply(fin, d), Comma, Sp,
            Open, gram, Sp, Minus, Sp, D(1), Close, Sp, Times, Sp, entry,
            Sp, Eq, Sp, D(0));

        return Disp(Seq(
            Forall, Sp, d, Comma, Sp, e, Colon, Sp, F.Id("Nat"), Comma, Sp,
            record, Colon, Sp, recordType, Comma, Sp,
            rho, Colon, Sp, matrixType, Comma, Sp,
            fixedPoint, Sp, Iff, Sp, equations, Dot));
    }
}
