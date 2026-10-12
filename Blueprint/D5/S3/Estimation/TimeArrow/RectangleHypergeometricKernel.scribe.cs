using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class RectangleHypergeometricKernelDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Estimation/TimeArrow/RectangleHypergeometricKernel.";
    private static readonly LibraryNoteRef[] ClassicalTools =
    [
        LibraryNoteRef.Create("D5/L/Estimation/siegrist2026hypergeometric"),
        LibraryNoteRef.Create("D5/L/Estimation/lahirichatterjeemaiti2007hypergeometric"),
        LibraryNoteRef.Create("D5/L/Estimation/kolassali2010saddlepoint")
    ];

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The positive and negative departure counts belong to one native history. Their labelled margin events yield the exact hypergeometric intersection kernel, while the same four cells supply the full calibration counts.",
        H("Native labelled histograms and rectangle kernels"),
        Blocks(
            Paragraph(Text("Use the complete collapsed-history fiber and conditionalFiberMass of NativeSignalConditionalFiber. signedDepartureBlocks 0 and 1 are the erased departure sites with positive and negative successor signs. jointRowHistogramEvent specifies both signal-row count multisets. The two words are coordinates of one history; no independence between arbitrary histories is asserted.")),
            Paragraph(Text("For finite V and R, intersectionEvent V R U t consists of B subset V with |B|=U and |B intersection R|=t. Binomial coefficients and differences in their arguments are natural-valued, so impossible intersections have zero count. nativeRectangleRows consists of supported rows whose positive count is k or k+1 and negative count is l or l+1. nativeRectangleACount counts its rows with positive count k and negative count l.")),
            Paragraph(Text("nativeRectangleReadout retains the complete positive histogram, the rectangle, the negative counts outside it, and the negative low-count margin. nativeMarginRectangleReadout retains the rectangle, both labelled outside counts as an optional pair, and both low-count margins. nativeMarginRectangleEvent ranges over positive low-count subsets of size R and the specified family of negative low-count subsets.")),
            Paragraph(Text("nativeRowCell labels the four exact count pairs [(k,l),(k+1,l),(k,l+1),(k+1,l+1)] by 0,1,2,3 on supported rows and is none otherwise. nativeCalibrationCells collects all rows carrying a given cell label.")),
            Theorem("native-joint-row-histogram-law", "NativeSignalConditionalFiber.native_joint_row_histogram_law",
                "For every natural M, q, s, support S : Support M q, real r, experiment e in {pair,path} and complete history o : Obs M s e, with finite Sites s e, 1 <= q < M, 0 < r < 1 and 0 <= compensation M q r < 1, for any signal-row multisets ap,am whose cardinalities equal the respective signedDepartureBlocks 0 and 1 cardinalities, conditionalFiberMass S r e o (jointRowHistogramEvent S e o ap am) equals multinomial(univ,ap.count)*multinomial(univ,am.count)/q^(|signedDepartureBlocks 0|+|signedDepartureBlocks 1|), with the multinomial coefficients cast to reals."),
            Theorem("log-factorial-envelopes", "NativeCalibratedArithmeticBridge.log_factorial_envelopes",
                "For every natural n>0, n*log n-n+(log n)/2 <= log(n!) <= n*log n-n+(log n)/2+1, with n and n! cast to reals. These scalar envelopes follow from classical Stirling inequalities."),
            Theorem("rectangle-intersection-card", "RectangleHypergeometricKernel.rectangle_intersection_card",
                "For every type alpha with decidable equality, finite sets V,R : Finset alpha and natural U,t, if R is a subset of V and t<=U, |intersectionEvent V R U t| = choose(|R|,t)*choose(|V|-|R|,U-t). No upper bounds on U or t by |V| or |R| are added."),
            Theorem("native-rectangle-readout-fiber", "RectangleHypergeometricKernel.native_rectangle_readout_fiber",
                "For every natural M, q, s, support S : Support M q, experiment e in {pair,path} and complete history o : Obs M s e, with finite Fiber S e o, for every positive histogram ap, signal-row set V, outside negative-count function outside and natural k,l,U, assume each i in V has ap.count i=k or k+1, and each i outside V fails the conjunction (ap.count i=k or k+1) and (outside i=l or l+1). Then nativeRectangleEvent S e o ap V outside l (V.powersetCard U) is exactly the set of y in the complete fiber for which nativeRectangleReadout S e o k l y = rectangleEnvironmentData ap V outside U."),
            Theorem("native-margin-rectangle-hypergeometric-law", "RectangleHypergeometricKernel.native_margin_rectangle_hypergeometric_law",
                "For every natural M, q, s, support S : Support M q, real r, experiment e in {pair,path} and complete history o : Obs M s e, with finite Sites s e, 1 <= q < M, 0 < r < 1 and 0 <= compensation M q r < 1, take a signal-row set V, outside count functions outsideP,outsideM and natural k,l,R,U,t. Assume sum_{i outside V} outsideP(i)+R*k+(|V|-R)*(k+1)=|signedDepartureBlocks 0| and sum_{i outside V} outsideM(i)+U*l+(|V|-U)*(l+1)=|signedDepartureBlocks 1|, with R<=|V|, U<=|V| and t<=U. The conditional mass of nativeMarginRectangleEvent with negative-subset family A |-> intersectionEvent V A U t, divided by the mass of the same event with family A |-> V.powersetCard U, equals choose(R,t)*choose(|V|-R,U-t)/choose(|V|,U). The quotients and binomial coefficients are real-valued; no denominator-positivity hypothesis is imposed."),
            Theorem("native-margin-rectangle-readout-fiber", "RectangleHypergeometricKernel.native_margin_rectangle_readout_fiber",
                "For every natural M, q, s, support S : Support M q, experiment e in {pair,path} and complete history o : Obs M s e, with finite Fiber S e o, take a signal-row set V, outside count functions outsideP,outsideM and natural k,l,R,U. Suppose every i outside V fails the conjunction (outsideP(i)=k or k+1) and (outsideM(i)=l or l+1). Then nativeMarginRectangleEvent S e o V outsideP outsideM k l R (A |-> V.powersetCard U) is exactly the fiber event nativeMarginRectangleReadout S e o k l y = (V, i |-> none if i is in V and some(outsideP(i),outsideM(i)) otherwise, R,U)."),
            Theorem("native-row-cell-iff", "SharedRectangleCalibration.native_row_cell_iff",
                "For every natural M, q, s, support S : Support M q, experiment e in {pair,path} and complete history o : Obs M s e, for every natural k,l, row i : Fin M and j : Fin 4, nativeRowCell S e o k l i = some j if and only if i is in S.val, count e o i 1 = k+[0,1,0,1](j) and count e o i (-1) = l+[0,0,1,1](j)."),
            Theorem("native-calibration-counts-margins", "SharedRectangleCalibration.native_calibration_counts_margins",
                "For every natural M, q, s, support S : Support M q, experiment e in {pair,path} and complete history o : Obs M s e, for every natural k,l and y : Fiber S e o, let V=nativeRectangleRows S e o k l y and C(j)=|nativeCalibrationCells S e y.val k l j|. Then |V|=C(0)+C(1)+C(2)+C(3), |{i in V: count e y.val i.val 1=k}|=C(0)+C(2), |{i in V: count e y.val i.val (-1)=l}|=C(0)+C(1), and nativeRectangleACount S e o k l y=C(0)."),
            Paragraph(Text("Finite-sampling kernels and factorial estimates are classical tools. The exact identification with the native joint histogram, the labelled conditioning event and the calibration counts is repo-derived. Hypergeometric approximation and saddlepoint references do not by themselves identify these native events. See "),
                Ref("D5/L/Estimation/siegrist2026hypergeometric"), Text("; "), Ref("D5/L/Estimation/lahirichatterjeemaiti2007hypergeometric"), Text("; "), Ref("D5/L/Estimation/kolassali2010saddlepoint"), Text("."))
        )));

    private static DocumentBlock.Describe Theorem(string id, string name, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + name),
            H(name), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(ClassicalTools),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);
}
