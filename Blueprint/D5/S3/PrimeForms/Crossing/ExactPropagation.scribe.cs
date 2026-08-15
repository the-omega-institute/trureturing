using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.Crossing;

internal sealed class ExactPropagationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The positive-cone crossing sandwich lowers the exact winding phase by two.",
        H("Exact Positive-Cone Propagation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exact-positive-cone-propagation"),
                DeclarationHandle.Create(
                    "D5/S3/PrimeForms/Crossing/ExactPropagation."
                    + "exact_propagation_positive_cone"),
                H("The crossing sandwich lowers the winding phase by two"),
                StatementSource.FromAuthor(PropagationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let T, b, and c be natural numbers with 2 <= T, b <= c, and "
                            + "b^2 + c^2 + 1 = T^2 + bc. Define gamma = "
                            + "[[T+c-b,b],[c,T+b-c]] and M = [[3,1],[2,1]]. The cone "
                            + "equation forces every coefficient used by the phase formula to be "
                            + "positive; in particular T+b-c > 0.")),
                    Paragraph(Text(
                        "Direct multiplication gives the complete lower-left chain c, 2, "
                            + "c+2T+2b, and 8T+7c. Completing the square in the cone equation "
                            + "gives c-b <= sqrt(T^2-1), while sqrt(T^2-1) < T. These two bounds "
                            + "prove the displayed inequality and make the endpoint sign "
                            + "corrections positive.")),
                    Paragraph(Text(
                        "The phase proof uses the repository's finite rational Dedekind sum and "
                            + "its proved reciprocity theorem. A residue-permutation argument "
                            + "first proves invariance under inverse numerators. Two reciprocity "
                            + "calculations then establish the right and left multiplication "
                            + "corrections separately, each with correction -3; no cocycle law is "
                            + "assumed. Since the fixed matrix has Phi(M)=2, the winding phase of "
                            + "M gamma M is exactly Psi(gamma)-2.")),
                    Paragraph(Text(
                        "Local searches in D5 and pinned Mathlib found no ready-made Rademacher "
                            + "phase or cocycle theorem. The exact imported hits are the finite "
                            + "Dedekind sum, its residue-permutation lemma, and Dedekind "
                            + "reciprocity. Loogle returned Unknown identifier Rademacher; the "
                            + "grep.app query returned HTTP 503, and the attempted LeanSearch "
                            + "endpoint returned HTTP 404."))),
                DescribeRole.Theorem))));

    private static Formula PropagationFormula()
    {
        Formula phase = Seq(Operatorname, Grp(F.Id("Phi")));
        Formula winding = Seq(Operatorname, Grp(F.Id("Psi")));
        Formula trace = Seq(Operatorname, Grp(F.Id("tr")));

        return Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Forall, Sp, F.Id("T"), Comma, F.Id("b"), Comma, F.Id("c"), InMacro,
        Mathbb, Grp(F.Id("N")), Comma, Quad, Sp,
        D(2), Leq, Sp, F.Id("T"), Comma, Quad, Sp,
        F.Id("b"), Leq, Sp, F.Id("c"), Comma, Quad, Sp,
        F.Id("b"), Caret, D(2), Plus, F.Id("c"), Caret, D(2), Plus, D(1), Eq,
        F.Id("T"), Caret, D(2), Plus, F.Id("b"), F.Id("c"), Longrightarrow, RowBreak,
        GammaLower, Eq, Begin, Grp(F.Id("pmatrix")),
        F.Id("T"), Plus, F.Id("c"), Minus, F.Id("b"), Amp, F.Id("b"), RowBreak,
        F.Id("c"), Amp, F.Id("T"), Plus, F.Id("b"), Minus, F.Id("c"),
        End, Grp(F.Id("pmatrix")), Comma, Quad, Sp,
        F.Id("M"), Eq, Begin, Grp(F.Id("pmatrix")),
        D(3), Amp, D(1), RowBreak, D(2), Amp, D(1), End, Grp(F.Id("pmatrix")), Comma, RowBreak,
        Open, F.Id("c"), Underscore, GammaLower, Comma, F.Id("c"), Underscore, F.Id("M"), Comma,
        F.Id("c"), Underscore, Grp(GammaLower, Sp, F.Id("M")), Comma,
        F.Id("c"), Underscore, Grp(F.Id("M"), GammaLower, Sp, F.Id("M")), Close,
        Eq, Open, F.Id("c"), Comma, D(2), Comma,
        F.Id("c"), Plus, D(2), F.Id("T"), Plus, D(2), F.Id("b"), Comma,
        D(8), F.Id("T"), Plus, D(7), F.Id("c"), Close, Comma, RowBreak,
        F.Id("c"), Plus, D(2), F.Id("T"), Plus, D(2), F.Id("b"), Geq,
        D(2), F.Id("c"), Plus, D(2), Open, F.Id("T"), Minus,
        Sqrt, Grp(F.Id("T"), Caret, D(2), Minus, D(1)), Close, Gt, D(0), Comma, RowBreak,
        F.Id("c"), Underscore, GammaLower, TraceProduct(trace, GammaLower), Gt, D(0), Comma, Quad, Sp,
        F.Id("c"), Underscore, Grp(F.Id("M"), GammaLower, Sp, F.Id("M")),
        TraceProduct(trace, F.Id("M"), GammaLower, Sp, F.Id("M")), Gt, D(0), Comma, RowBreak,
        phase, Open, F.Id("M"), Close, Eq, D(2), Comma, Quad, Sp,
        phase, Open, GammaLower, Sp, F.Id("M"), Close, Eq,
        phase, Open, GammaLower, Close, Plus, phase, Open, F.Id("M"), Close, Minus, D(3), Comma, RowBreak,
        phase, Open, F.Id("M"), GammaLower, Sp, F.Id("M"), Close, Eq,
        phase, Open, F.Id("M"), Close, Plus, phase, Open, GammaLower, Sp, F.Id("M"), Close, Minus, D(3), Comma, RowBreak,
        winding, Open, F.Id("M"), GammaLower, Sp, F.Id("M"), Close, Eq,
        winding, Open, GammaLower, Close, Minus, D(2), Dot,
        End, Grp(F.Id("gathered"))));
    }

    private static Formula TraceProduct(Formula trace, params Formula[] matrix) =>
        Seq(trace, Open, Seq(matrix), Close);
}
