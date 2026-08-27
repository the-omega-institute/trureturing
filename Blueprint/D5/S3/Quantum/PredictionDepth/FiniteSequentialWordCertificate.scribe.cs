using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PredictionDepth;

internal sealed class FiniteSequentialWordCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete centered sequential word effects admit dimension-bounded finite certificates.",
        H("Finite Sequential Word Certificate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-sequential-word-certificate"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/PredictionDepth/FiniteSequentialWordCertificate."
                        + "finite_sequential_word_certificate"),
                H("Complete finite words have dimension-bounded certificates"),
                StatementSource.FromAuthor(CertificateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Each word acts on the identity Hermitian effect through the imported "
                            + "sequentialWordEffect construction. The imported centeredEffect "
                            + "operation removes its scalar trace component on the exact real "
                            + "trace-zero Hermitian carrier.")),
                    Paragraph(Text(
                        "If the centered effects of all finite words span that carrier, finite-"
                            + "dimensional basis extraction selects a concrete finite word set "
                            + "with at most d squared minus one members and the same span.")),
                    Paragraph(Text(
                        "For the depth clause, the uncentered bounded-word spans start with the "
                            + "identity line. Once two consecutive stages agree, prefix closure "
                            + "under every instrument generator makes that equality permanent. "
                            + "Their rank can therefore grow strictly at most d squared minus "
                            + "one times, after which canonical centering gives the full bounded "
                            + "centered span."))),
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

    private static Formula CertificateFormula()
    {
        Formula d = F.Id("d");
        Formula alphabet = F.Id("A");
        Formula instrumentDual = F.Id("J");
        Formula word = F.Id("w");
        Formula selected = F.Id("W");
        Formula depth = F.Id("n");
        Formula effect = F.Id("e");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula nat = Seq(Operatorname, Grp(F.Id("Nat")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula wordType = Call("List", alphabet);
        Formula hermitian = Call("HermitianSpace", d);
        Formula traceZero = Call("traceZeroHermitian", d);
        Formula dualMap = Call("LinearMap", real, hermitian, hermitian);
        Formula wordEffect = Call("sequentialWordEffect", instrumentDual, word);
        Formula centeredWord = Call("centeredHermitianMap", d, wordEffect);
        Formula dimensionBound = Seq(new Formula.Power(d, D(2)), Minus, D(1));
        Formula completeSet = Seq(
            OpenBrace, centeredWord, Colon, Sp, word, Colon, Sp, wordType, CloseBrace);
        Formula completeSpan = Seq(
            Call("span", real, completeSet), Sp, Eq, Sp, traceZero);
        Formula selectedSet = Seq(
            OpenBrace, centeredWord, Colon, Sp, word, InMacro, Sp, selected, CloseBrace);
        Formula selectedSpan = Seq(
            Call("span", real, selectedSet), Sp, Eq, Sp, traceZero);
        Formula selectedBound = Seq(
            Call("card", selected), Sp, Leq, Sp, dimensionBound);
        Formula boundedSet = Seq(
            OpenBrace, effect, Colon, Sp, traceZero, Sp, Mid, Sp,
            Exists, Sp, word, Colon, Sp, wordType, Comma, Sp,
            Call("length", word), Sp, Leq, Sp, depth, Sp, Land, Sp,
            effect, Sp, Eq, Sp, centeredWord, CloseBrace);
        Formula boundedSpan = Seq(
            Call("span", real, boundedSet), Sp, Eq, Sp, traceZero);

        return Disp(Seq(
            Forall, Sp, d, Colon, Sp, nat, Comma, Sp, Call("NeZero", d), Comma,
            RowBreak, Grp(),
            alphabet, Colon, Sp, type, Comma, RowBreak, Grp(),
            instrumentDual, Colon, Sp, alphabet, Sp, To, Sp, dualMap, Comma,
            RowBreak, Grp(),
            completeSpan, Sp, Rightarrow, RowBreak, Grp(),
            Open, Exists, Sp, selected, Colon, Sp, Call("Finset", wordType), Comma, Sp,
            selectedBound, Sp, Land, RowBreak, Grp(),
            selectedSpan, Close, Sp, Land, RowBreak, Grp(),
            Open, Exists, Sp, depth, Colon, Sp, nat, Comma, Sp,
            depth, Sp, Leq, Sp, dimensionBound, Sp, Land, RowBreak, Grp(),
            boundedSpan, Close, Dot));
    }
}
