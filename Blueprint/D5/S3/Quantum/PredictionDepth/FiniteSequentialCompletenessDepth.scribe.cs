using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PredictionDepth;

internal sealed class FiniteSequentialCompletenessDepthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete finite sequential word spans reach the full Hermitian carrier at bounded depth.",
        H("Finite Sequential Completeness Depth"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-sequential-completeness-depth"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/PredictionDepth/FiniteSequentialCompletenessDepth."
                        + "finite_sequential_completeness_depth"),
                H("Finite-word completeness has a bounded-depth witness"),
                StatementSource.FromAuthor(CompletenessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Each finite word acts on the identity Hermitian effect through the "
                            + "canonical sequentialWordEffect construction on the full real "
                            + "Hermitian carrier.")),
                    Paragraph(Text(
                        "Canonical trace removal transfers full-span completeness to the real "
                            + "trace-zero carrier, where the frozen finite-word certificate gives "
                            + "the depth bound. Adding back the identity component returns the "
                            + "bounded span to the source's full Hermitian carrier."))),
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

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula CompletenessFormula()
    {
        Formula d = F.Id("d");
        Formula alphabet = F.Id("A");
        Formula instrumentDual = F.Id("J");
        Formula word = F.Id("w");
        Formula depth = F.Id("n");
        Formula effect = F.Id("e");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula nat = Seq(Operatorname, Grp(F.Id("Nat")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula wordType = Call("List", alphabet);
        Formula hermitian = Call("HermitianSpace", d);
        Formula dualMap = Call("LinearMap", real, hermitian, hermitian);
        Formula wordEffect = Call("sequentialWordEffect", instrumentDual, word);
        Formula dimensionBound = Seq(new Formula.Power(d, D(2)), Minus, D(1));
        Formula completeSet = Seq(
            OpenBrace, wordEffect, Colon, Sp, word, Colon, Sp, wordType, CloseBrace);
        Formula completeSpan = Seq(
            Call("span", real, completeSet), Sp, Eq, Sp, hermitian);
        Formula boundedSet = Seq(
            OpenBrace, effect, Colon, Sp, hermitian, Sp, Mid, Sp,
            Exists, Sp, word, Colon, Sp, wordType, Comma, Sp,
            Call("length", word), Sp, Leq, Sp, depth, Sp, Land, Sp,
            effect, Sp, Eq, Sp, wordEffect, CloseBrace);
        Formula boundedSpan = Seq(
            Call("span", real, boundedSet), Sp, Eq, Sp, hermitian);

        return Disp(Seq(
            Forall, Sp, d, Colon, Sp, nat, Comma, Sp, Call("NeZero", d), Comma,
            RowBreak, Grp(),
            alphabet, Colon, Sp, type, Comma, RowBreak, Grp(),
            instrumentDual, Colon, Sp, alphabet, Sp, To, Sp, dualMap, Comma,
            RowBreak, Grp(),
            completeSpan, Sp, Rightarrow, RowBreak, Grp(),
            Exists, Sp, depth, Colon, Sp, nat, Comma, Sp,
            depth, Sp, Leq, Sp, dimensionBound, Sp, Land, RowBreak, Grp(),
            boundedSpan, Dot));
    }
}
