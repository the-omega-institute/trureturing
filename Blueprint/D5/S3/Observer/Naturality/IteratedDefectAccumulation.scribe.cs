using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Naturality;

internal sealed class IteratedDefectAccumulationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Orbitwise naturality defects accumulate with Lipschitz weights.",
        H("Iterated Defect Accumulation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("iterated-naturality-defect-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Naturality/IteratedDefectAccumulation."
                        + "iterated_naturality_defect_bound"),
                H("Iterated naturality defect bound"),
                StatementSource.FromAuthor(DefectBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let tau update the concrete state space Y, let sigma be an "
                            + "L-Lipschitz update of the observed space Z, and let pi project "
                            + "concrete states into Z.")),
                    Paragraph(Text(
                        "After n updates, the distance between projecting the concrete orbit "
                            + "and following the abstract orbit is bounded by the sum of the "
                            + "one-step naturality defects along the concrete orbit. A defect "
                            + "at step k is weighted by the remaining n minus 1 minus k abstract "
                            + "updates.")),
                    Paragraph(Text(
                        "The proof is by induction. At a successor step, the triangle inequality "
                            + "separates the newest local defect from the previous accumulated "
                            + "error, and Lipschitz continuity multiplies the latter by L.")),
                    Paragraph(Text(
                        "Repository search found only a weaker uniform-defect bound. Local "
                            + "mathlib search found no complete nonuniform accumulation theorem; "
                            + "the proof applies LipschitzWith.edist_le_mul, the successor rule "
                            + "for function iterates, and Finset.sum_range_succ."))),
                DescribeRole.Theorem))));

    private static Formula Iterate(Formula map, Formula exponent, Formula state) =>
        Seq(map, Caret, Grp(exponent), Open, state, Close);

    private static Formula Apply(Formula map, Formula state) =>
        Seq(map, Open, state, Close);

    private static Formula Distance(Formula left, Formula right) =>
        Seq(F.Id("d"), Underscore, Grp(F.Id("Z")), Open, left, Comma, Sp, right, Close);

    private static Formula DefectBoundFormula()
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula y = F.Id("y");
        Formula l = F.Id("L");
        Formula concreteOrbit = Iterate(Tau, n, y);
        Formula partialOrbit = Iterate(Tau, k, y);
        Formula lhs = Distance(
            Apply(Pi, concreteOrbit),
            Iterate(SigmaLower, n, Apply(Pi, y)));
        Formula localDefect = Distance(
            Apply(Pi, Apply(Tau, partialOrbit)),
            Apply(SigmaLower, Apply(Pi, partialOrbit)));
        Formula weightedSum = Seq(
            Sum, Underscore, Grp(Seq(k, Eq, D(0))), Caret,
            Grp(Seq(n, Minus, D(1))), Sp,
            l, Caret, Grp(Seq(n, Minus, D(1), Minus, k)), Sp,
            localDefect);

        return Disp(Seq(
            Forall, Sp, n, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Forall, Sp, y, Sp, InMacro, Sp, F.Id("Y"), Comma, Esc,
            lhs, Sp, Leq, Sp, weightedSum, Dot));
    }
}
