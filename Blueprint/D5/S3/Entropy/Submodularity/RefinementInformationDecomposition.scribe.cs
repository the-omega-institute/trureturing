using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Submodularity;

internal sealed class RefinementInformationDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Predictive memory decomposes exactly across a finer deterministic readout.",
        H("Predictive Memory under Deterministic Refinement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("deterministic-refinement-information-decomposition"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Submodularity/RefinementInformationDecomposition."
                        + "deterministic_refinement_information_decomposition"),
                H("Deterministic refinement gives an exact nonnegative information gain"),
                StatementSource.FromAuthor(DecompositionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let p be a normalized nonnegative joint mass function on a finite past "
                            + "P and future F. Let q prime map the past to a finer finite readout, "
                            + "and let f deterministically forget that readout to a coarser one.")),
                    Paragraph(Text(
                        "The coarse readout is constructed as f composed with q prime. Predictive "
                            + "memory is the imported conditional mutual information between past "
                            + "and future given the named readout. The gain is the conditional "
                            + "mutual information between the fine readout and future given the "
                            + "coarse readout.")),
                    Paragraph(Text(
                        "The displayed equality and nonnegativity are both public conjuncts. No "
                            + "independence between P and the finer readout is assumed: its law is "
                            + "the deterministic pushforward of the same past/future law.")),
                    Paragraph(Text(
                        "The proof applies the frozen conditional-information entropy-defect and "
                            + "nonnegativity theorems to the graph-supported induced laws. Exact "
                            + "finite-sum identities identify the coarse law as the pushforward of "
                            + "the fine law."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Fintype(Formula carrier) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, carrier, Close,
            CloseBracket);

    private static Formula DecompositionFormula()
    {
        Formula past = F.Id("P");
        Formula future = F.Id("F");
        Formula fineCarrier = F.Id("Fine");
        Formula coarseCarrier = F.Id("Coarse");
        Formula p = F.Id("p");
        Formula z = F.Id("z");
        Formula fine = F.Id("q");
        Formula forget = F.Id("f");
        Formula pz = Seq(p, Open, z, Close);
        Formula law = Seq(
            Open, Forall, Sp, z, Comma, Sp, D(0), Sp, Leq, Sp, pz, Close,
            Sp, Land, Sp, Sum, Underscore, Grp(z), Sp, pz, Sp, Eq, Sp, D(1));
        Formula coarse = Seq(forget, Sp, Circ, Sp, fine);
        Formula coarseMemory = Call("predictiveMemory", p, coarse);
        Formula fineMemory = Call("predictiveMemory", p, fine);
        Formula gain = Call("refinementGain", p, fine, forget);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, past, Comma, Sp, future, Comma, Sp,
            fineCarrier, Comma, Sp, coarseCarrier, Comma, RowBreak, Grp(),
            Fintype(past), Sp, Fintype(future), Sp,
            Fintype(fineCarrier), Sp, Fintype(coarseCarrier), Comma, RowBreak, Grp(),
            p, Colon, Sp, past, Sp, Times, Sp, future, Sp, To, Sp,
            Mathbb, Grp(F.Id("R")), Comma,
            RowBreak, Grp(),
            law, Sp, Rightarrow, RowBreak, Grp(),
            Forall, Sp, fine, Colon, Sp, past, Sp, To, Sp, fineCarrier, Comma, Sp,
            forget, Colon, Sp, fineCarrier, Sp, To, Sp, coarseCarrier, Comma,
            RowBreak, Grp(),
            Open, coarseMemory, Sp, Minus, Sp, fineMemory, Sp, Eq, Sp, gain, Close,
            Sp, Land, RowBreak, Grp(),
            D(0), Sp, Leq, Sp, gain, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
