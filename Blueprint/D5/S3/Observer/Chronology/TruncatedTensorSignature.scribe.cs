using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class TruncatedTensorSignatureDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/TruncatedTensorSignature.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Universal degree-two tensor signatures obey Chen concatenation.",
        H("Truncated Tensor Signature"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("tensor-signature"),
                DeclarationHandle.Create(Prefix + "TensorSignature"),
                H("Tensor-square signature"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The universal step-two coordinate stores degree one in a module and "
                        + "twice degree two in its genuine tensor square."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("event-signature"),
                DeclarationHandle.Create(Prefix + "eventTensorSignature"),
                H("Single-event tensor signature"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "One event contributes its vector and its pure tensor square."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("word-signature"),
                DeclarationHandle.Create(Prefix + "chronologicalTensorSignature"),
                H("Chronological tensor word signature"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A list is folded from left to right using chronological tensor composition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("chen-append"),
                DeclarationHandle.Create(Prefix + "chronological_tensor_signature_append"),
                H("Tensor Chen concatenation"),
                StatementSource.FromAuthor(AppendFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The signature of an earlier word followed by a later word is their "
                        + "chronological product."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("degree-one"),
                DeclarationHandle.Create(Prefix + "chronological_tensor_signature_degree_one"),
                H("Degree-one word sum"),
                StatementSource.FromAuthor(DegreeOneFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The degree-one coordinate is the ordinary sum of all event vectors."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-events"),
                DeclarationHandle.Create(Prefix + "chronological_tensor_signature_two_events"),
                H("Explicit two-event signature"),
                StatementSource.FromAuthor(TwoEventFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two events exhibit the pure squares and twice the ordered tensor cross term."))),
                DescribeRole.Theorem)),
        []));

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

    private static Formula Sig(Formula word) =>
        Call("chronologicalTensorSignature", F.Id("f"), word);

    private static Formula Tensor(Formula left, Formula right) =>
        Call("tensor", left, right);

    private static Formula PairWord(Formula first, Formula second) =>
        Seq(OpenBracket, first, Comma, Sp, second, CloseBracket);

    private static Formula AppendFormula() => Disp(Seq(
        Forall, Sp, F.Id("f"), Comma, Sp, F.Id("P"), Comma, Sp, F.Id("S"),
        Comma, Sp,
        Sig(Call("append", F.Id("P"), F.Id("S"))), Sp, Eq, Sp,
        Sig(F.Id("P")), Sp, Cdot, Sp, Sig(F.Id("S")), Dot));

    private static Formula DegreeOneFormula() => Disp(Seq(
        Forall, Sp, F.Id("f"), Comma, Sp, F.Id("L"), Comma, Sp,
        Call("degreeOne", Sig(F.Id("L"))), Sp, Eq, Sp,
        Call("sum", Call("map", F.Id("f"), F.Id("L"))), Dot));

    private static Formula TwoEventFormula() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Call("degreeOne", Sig(PairWord(F.Id("x"), F.Id("y")))),
        Sp, Eq, Sp, F.Id("x"), Sp, Plus, Sp, F.Id("y"), RowBreak,
        Call("doubledDegreeTwo", Sig(PairWord(F.Id("x"), F.Id("y")))),
        Sp, Eq, Sp,
        Tensor(F.Id("x"), F.Id("x")), Sp, Plus, Sp,
        D(2), Sp, Cdot, Sp, Tensor(F.Id("x"), F.Id("y")), Sp, Plus, Sp,
        Tensor(F.Id("y"), F.Id("y")),
        End, Grp(F.Id("gathered"))));
}
