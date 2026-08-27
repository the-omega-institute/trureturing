using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PredictionDepth;

internal sealed class UnifiedSequentialKernelDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/PredictionDepth/UnifiedSequentialKernel."
            + "unified_sequential_kernel";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All allowed sequential statistics determine one orthogonal residual.",
        H("Unified Sequential Kernel"),
        Blocks(Describe.Lean(
            DescribeId.Create("unified-sequential-kernel"),
            DeclarationHandle.Create(Declaration),
            H("Allowed word equivalence is residual membership"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The observer supplies an allowed set of finite branch words. Each word "
                        + "uses the canonical source-order Heisenberg fold on the identity "
                        + "effect.")),
                Paragraph(Text(
                    "Two represented states agree on every allowed word exactly when their "
                        + "difference lies in the orthogonal complement of the real span of "
                        + "all allowed word effects."))),
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

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d");
        Formula alphabet = F.Id("A");
        Formula state = F.Id("S");
        Formula allowed = F.Id("W");
        Formula word = F.Id("w");
        Formula instrumentDual = F.Id("J");
        Formula representation = F.Id("X");
        Formula rho = F.Id("rho");
        Formula sigma = F.Id("sigma");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula carrier = Call("HermitianSpace", d);
        Formula wordType = Call("List", alphabet);
        Formula wordEffect = Call("sequentialWordEffect", instrumentDual, word);
        Formula expectation(Formula value) =>
            Call("inner", real, Apply(representation, value), wordEffect);
        Formula agrees = Seq(
            Forall, Sp, word, Colon, Sp, wordType, Comma, Sp,
            word, Sp, InMacro, Sp, allowed, Sp, Rightarrow, Sp,
            expectation(rho), Sp, Eq, Sp, expectation(sigma));
        Formula allowedEffects = Seq(
            OpenBrace, Call("sequentialWordEffect", instrumentDual, word), Sp,
            Mid, Sp, word, Sp, InMacro, Sp, allowed, CloseBrace);
        Formula residual = Seq(
            Open, Call("span", real, allowedEffects), Close,
            Caret, Grp(Perp));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, d, Colon, Sp, F.Id("Nat"), Comma, Sp,
            alphabet, Comma, Sp, state, Colon, Sp,
            Seq(Operatorname, Grp(F.Id("Type"))), Comma, RowBreak, Grp(),
            allowed, Colon, Sp, Call("Set", wordType), Comma, Sp,
            instrumentDual, Colon, Sp, alphabet, To, carrier, To, carrier,
            Comma, RowBreak, Grp(),
            representation, Colon, Sp, state, To, carrier, Comma, Sp,
            rho, Comma, Sp, sigma, Colon, Sp, state, Sp, Rightarrow,
            RowBreak, Grp(),
            Open, agrees, Close, Sp, Leftrightarrow, Sp,
            Open, Apply(representation, rho), Sp, Minus, Sp,
            Apply(representation, sigma), Sp, InMacro, Sp, residual, Close,
            Dot, End, Grp(F.Id("gathered"))));
    }
}
