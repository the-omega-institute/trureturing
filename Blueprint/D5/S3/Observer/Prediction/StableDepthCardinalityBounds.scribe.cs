using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Prediction;

internal sealed class StableDepthCardinalityBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stable prediction depth is bounded by the available complete-future quotient classes.",
        H("Stable Depth Cardinality Bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("stable-depth-runtime-and-token-bounds"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Prediction/StableDepthCardinalityBounds."
                    + "stable_depth_runtime_and_token_bounds"),
                H("Stable depth bounds for finite runtimes and token carriers"),
                StatementSource.FromAuthor(BoundsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Y be a nonempty finite deterministic runtime, let F update its state, "
                            + "and let q map Y surjectively onto the actual output carrier O. The "
                            + "least stable depth is defined by equality of two consecutive "
                            + "finite-future readout relations, while the complete relation compares "
                            + "all future readout coordinates.")),
                    Paragraph(Text(
                        "The stable finite relation equals the complete-future relation. Therefore "
                            + "the exact finite refinement bound identifies the terminal class count "
                            + "with the cardinality of Y modulo complete-future equality and the "
                            + "initial class count with the cardinality of O.")),
                    Paragraph(Text(
                        "For a minimal length-L token model, the runtime carrier is the full function "
                            + "type from Fin L to the token alphabet Sigma and the surjective output "
                            + "carrier is Sigma itself. The finite function-cardinality formula then "
                            + "specializes the general bound to |Sigma|^L - |Sigma|.")),
                    Paragraph(Text(
                        "The source's final bullets distinguish prediction-classification depth from "
                            + "degradation time, parameter count, cycle-entry time, and semantic memory. "
                            + "Those explanatory contrasts introduce no in-scope predicates and are "
                            + "not asserted as invented universal clauses."))),
                DescribeRole.Theorem))));

    private static Formula Cardinality(Formula value) =>
        Seq(Lvert, Sp, value, Sp, Rvert);

    private static Formula Typeclass(string name, Formula type) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, type, Close, CloseBracket);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula BoundsFormula()
    {
        Formula state = F.Id("Y");
        Formula output = F.Id("O");
        Formula update = F.Id("F");
        Formula readout = F.Id("q");
        Formula alphabet = Sigma;
        Formula length = F.Id("L");
        Formula tokenState = Seq(alphabet, Caret, Grp(length));
        Formula tokenUpdate = F.Id("F"), tokenReadout = F.Id("r");
        Formula depth = new Formula.Subscript(F.Id("m"), Star);
        Formula infiniteRelation = Seq(Equiv, Underscore, Grp(Infty));
        Formula completionCount = Cardinality(Seq(state, Slash, infiniteRelation));
        Formula outputCount = Cardinality(output);
        Formula stateCount = Cardinality(state);
        Formula generalGap = Seq(completionCount, Sp, Minus, Sp, outputCount);
        Formula stateGap = Seq(stateCount, Sp, Minus, Sp, outputCount);
        Formula tokenDepth = Seq(depth, Open, tokenUpdate, Comma, Sp, tokenReadout, Close);
        Formula tokenGap = Seq(
            Cardinality(alphabet), Caret, Grp(length), Sp, Minus, Sp,
            Cardinality(alphabet));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, output, Comma, Sp,
            Typeclass("Fintype", state), Comma, Sp,
            Typeclass("Fintype", output), Comma, Sp,
            Typeclass("Nonempty", state), Comma, RowBreak, Grp(),
            update, Colon, Sp, state, Sp, To, Sp, state, Comma, Sp,
            readout, Colon, Sp, state, Sp, To, Sp, output, Comma, Sp,
            Call("Surjective", readout), Comma, RowBreak, Grp(),
            Open, depth, Sp, Leq, Sp, generalGap, Sp, Leq, Sp, stateGap, Close,
            Sp, Land, Sp, RowBreak, Grp(),
            Open, Forall, Sp, alphabet, Comma, Sp, length, Comma, Sp,
            Typeclass("Fintype", alphabet), Comma, Sp,
            Typeclass("Nonempty", alphabet), Comma, RowBreak, Grp(),
            tokenUpdate, Colon, Sp, tokenState, Sp, To, Sp, tokenState, Comma, Sp,
            tokenReadout, Colon, Sp, tokenState, Sp, To, Sp, alphabet, Comma, Sp,
            Call("Surjective", tokenReadout), Sp, Rightarrow, Sp,
            tokenDepth, Sp, Leq, Sp, tokenGap, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
