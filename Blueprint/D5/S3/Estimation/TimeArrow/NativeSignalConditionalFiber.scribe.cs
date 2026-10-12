using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class NativeSignalConditionalFiberDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Estimation/TimeArrow/NativeSignalConditionalFiber.";
    private static readonly LibraryNoteRef[] ClassicalTools =
    [
        LibraryNoteRef.Create("D5/L/Estimation/siegrist2026hypergeometric"),
        LibraryNoteRef.Create("D5/L/Estimation/lecam1960poissonbinomial"),
        LibraryNoteRef.Create("D5/L/Estimation/grinsteadsnell2006probability")
    ];

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete collapsed pair or path history gives a uniform conditional law on erased signal labels. A single logistic calibration equation supplies the moving-root response and variance comparisons. The original integer floors retain explicit errors.",
        H("Native signal fibers, shared calibration, and integer floors"),
        Blocks(
            Paragraph(Text("Support M q consists of q labelled rows in Fin M. Fiber S e o contains exactly the histories with collapsedObs S e y = collapsedObs S e o. SignalSites S e o contains all erased vertex sites, including an erased terminal vertex in the path experiment. Departure counts do not include the terminal vertex. fiberLabelEquiv reconstructs the complete history from its erased labels. conditionalFiberMass is the original probability weight of an event divided by the original weight of the complete fiber, using real division also at zero.")),
            Paragraph(Text("Write sigma(x) = Real.sigmoid x. The offsets in A, B, C, D order are [0, log((1+r)/(1-epsilon)), log((1-r)/(1+epsilon)), log((1+r)/(1-epsilon))+log((1-r)/(1+epsilon))]. cellCounts N R U t is [t,U-t,R-t,N-R-U+t]. calibratedMean sums sigma over all outside rows plus the cell-count-weighted sigmoids. calibratedVariance is the same complete sum with sigma replaced by sigma*(1-sigma). checkerboard is sigma(x)+sigma(x+offset 3)-sigma(x+offset 1)-sigma(x+offset 2).")),
            Paragraph(Text("centralPositive r L is the natural floor of ((1+r)/2)*L; centralNegative r L is natural subtraction L-centralPositive r L. phi r = ((1+r)/2)*log(1+r)+((1-r)/2)*log(1-r), center r L = centralPositive r L*log(1+r)+centralNegative r L*log(1-r), and population r beta L = 2^floor(phi r*L/(beta*log 2)) with natural floor. Natural counts are cast to reals in real expressions.")),
            Theorem("native-fiber-departure-counts", "NativeSignalConditionalFiber.native_fiber_departure_counts",
                "For every natural M, q, s, support S : Support M q, experiment e in {pair,path} and complete history o : Obs M s e, for every y : Fiber S e o, row i : Fin M and real z, count e y.val i z equals the cardinality of the k : Fin s such that siteEquiv M s e y.val (departureSite s e k) = Sum.inl i and chi (siteEquiv M s e o (successorSite s e k)) = z. The departure identity is taken from y, and the successor sign from o."),
            Theorem("native-signal-assignment-law", "NativeSignalConditionalFiber.native_signal_assignment_law",
                "For every natural M, q, s, support S : Support M q, real r, experiment e in {pair,path} and complete history o : Obs M s e, with finite Sites s e, 1 <= q < M, 0 < r < 1 and 0 <= compensation M q r < 1, every finite set A of functions SignalSites S e o -> {i : Fin M // i in S.val} satisfies conditionalFiberMass S r e o (A.map (fiberLabelEquiv S e o).symm.toEmbedding) = |A|/q^(Nat.card (SignalSites S e o)). The event A is arbitrary; the empty event and histories of length zero remain in scope."),
            Theorem("native-departure-label-count", "NativeSignalConditionalFiber.native_departure_label_count",
                "For every natural M, q, s, support S : Support M q, experiment e in {pair,path} and complete history o : Obs M s e, with finite Sites s e, every y : Fiber S e o, supported row i : Fin M and real z satisfy count e y.val i z = departureLabelCount S e o (fiberLabelEquiv S e o y) i z."),
            Theorem("native-background-row-counts", "NativeSignalConditionalFiber.native_background_row_counts",
                "For every natural M, q, s, support S : Support M q, experiment e in {pair,path} and complete history o : Obs M s e, every y : Fiber S e o, row i : Fin M outside S.val and real z satisfy count e y.val i z = count e o i z."),
            Theorem("sigmoid-shift-deriv", "SharedRectangleCalibration.sigmoid_shift_deriv",
                "For all real a and x, the function u |-> sigma(u+a) has derivative sigma(x+a)*(1-sigma(x+a)) at x."),
            Theorem("moving-calibration-deriv", "SharedRectangleCalibration.moving_calibration_deriv",
                "For every finite type iota, outside : iota -> real and real r, epsilon, N, R, U, t, x, v and function theta : real -> real, if theta has derivative v at t and theta(t)=x, then u |-> calibratedMean outside r epsilon N R U u (theta(u)) has derivative checkerboard r epsilon x + calibratedVariance outside r epsilon N R U t x*v at t."),
            Theorem("shared-root-response", "SharedRectangleCalibration.shared_root_response",
                "For every finite type iota, outside : iota -> real and real r, epsilon, N, R, U, q, t, x, v and function theta : real -> real, suppose theta has derivative v at t, theta(t)=x, calibratedMean outside r epsilon N R U u (theta(u))=q throughout some neighborhood of t, and calibratedVariance outside r epsilon N R U t x is nonzero. Then v=-checkerboard r epsilon x/calibratedVariance outside r epsilon N R U t x."),
            Theorem("exists-shared-calibration-root", "SharedRectangleCalibration.exists_shared_calibration_root",
                "For every finite type iota, outside : iota -> real and real r, epsilon, N, R, U, q, t, x, if calibratedMean outside r epsilon N R U t x=q and calibratedVariance outside r epsilon N R U t x is nonzero, there exists theta : real -> real with theta(t)=x, calibratedMean outside r epsilon N R U u (theta(u))=q throughout some neighborhood of t, and derivative -checkerboard r epsilon x/calibratedVariance outside r epsilon N R U t x at t."),
            Theorem("compensated-group-deriv", "SharedRectangleCalibration.compensated_group_deriv",
                "For every finite type iota, outside : iota -> real and real r, epsilon, N, R, U, q, bg, t, x, v and function theta : real -> real, suppose theta has derivative v at t, theta(t)=x, the complete calibrated mean equals q throughout some neighborhood of t, and its variance at (t,x) is nonzero. Then u |-> (bg+u)*sigma(theta(u))-u/2 has derivative sigma(x)-1/2-(bg+t)*sigma(x)*(1-sigma(x))*checkerboard r epsilon x/calibratedVariance outside r epsilon N R U t x at t."),
            Theorem("checkerboard-negative-neighborhood", "SharedRectangleCalibration.checkerboard_negative_neighborhood",
                "For every real r with 0<r<1, there exists a real d>0 such that checkerboard r epsilon x < -d for all pairs (epsilon,x) in some neighborhood of (0,0). One d works throughout that neighborhood."),
            Theorem("exists-calibration-root", "SharedRectangleCalibration.exists_calibration_root",
                "For every finite type iota, outside : iota -> real and real r, epsilon, N, R, U, q, t, if 0<q<|iota|+N, there exists a real x with calibratedMean outside r epsilon N R U t x=q. Nonnegative cell counts are not a hypothesis of this existence statement."),
            Theorem("unique-shared-root", "SharedRectangleCalibration.unique_shared_root",
                "For every finite type iota, outside : iota -> real and real r, epsilon, N, R, U, q, t, if N>0, 0<q<|iota|+N and every cellCounts N R U t j is nonnegative, there exists exactly one real x with calibratedMean outside r epsilon N R U t x=q."),
            Theorem("shared-calibration-curve", "SharedRectangleCalibration.shared_calibration_curve",
                "For every finite type iota, outside : iota -> real and real r, epsilon, N, R, U, q, a, b, suppose N>0, 0<q<|iota|+N and all four cell counts are nonnegative at every t in the open interval (a,b). There exists one theta : real -> real such that, for every t in (a,b), calibratedMean outside r epsilon N R U t (theta(t))=q, theta has derivative -checkerboard r epsilon (theta(t))/calibratedVariance outside r epsilon N R U t (theta(t)) at t, and this same variance is strictly positive. No ordering hypothesis on a and b is imposed."),
            Theorem("sigmoid-variance-tilt", "RectangleCalibrationBounds.sigmoid_variance_tilt",
                "For all real x,h with 1/2<=exp(-h)<=2, sigma(x)*(1-sigma(x))/2 <= sigma(x+h)*(1-sigma(x+h)) <= 2*sigma(x)*(1-sigma(x))."),
            Theorem("central-fiber-variance-bounds", "RectangleCalibrationBounds.central_fiber_variance_bounds",
                "For every finite type iota, outside : iota -> real and real r, epsilon, N, R, U, t, t0, x, h, w, assume all cell counts at t are nonnegative, |t-t0|<=w and 1/2<=exp(-h)<=2. Then (calibratedVariance outside r epsilon N R U t0 x-w)/2 <= calibratedVariance outside r epsilon N R U t (x+h) <= 2*(calibratedVariance outside r epsilon N R U t0 x+w)."),
            Theorem("central-rounding", "NativeGrowthRounding.central_rounding",
                "For every real r with 0<=r<=1 and natural L, centralPositive r L<=L, the error ((1+r)/2)*L-centralPositive r L lies in [0,1), and the real cast of centralNegative r L equals L-centralPositive r L."),
            Theorem("center-rounding", "NativeGrowthRounding.center_rounding",
                "For every real r with 0<=r<1 and natural L, phi r*L-log((1+r)/(1-r)) <= center r L <= phi r*L."),
            Theorem("population-exponential-bounds", "NativeGrowthRounding.population_exponential_bounds",
                "For every real r,beta and natural L with phi r>=0 and beta>0, exp((phi r/beta)*L)/2 <= population r beta L <= exp((phi r/beta)*L)."),
            Theorem("information-rate-bounds", "NativeGrowthRounding.information_rate_bounds",
                "For every real r with 0<r<1, 0<phi r<log 2."),
            Theorem("original-count-rounding", "NativeRectangleReferenceRatios.original_count_rounding",
                "For every real r with 0<r<1 and natural L>=1, assume ((1+r)/2)*L>=15 and ((1-r)/2)*L>=30. Let k be the natural floor of ((1+r)/2)*L and l=L-k in the naturals. Then k<=L, k>0, l>0, 15/16<=L*(1+r)/(2*(k+1))<=1 and 15/16<=L*(1-r)/(2*(l+1))<=1."),
            Paragraph(Text("The finite-sampling, Poisson-binomial and elementary-probability references supply classical tools. The native-history identifications and the stated formal applications are repo-derived; the references do not identify this collapsed-history fiber or supply its shared calibration equation. See "),
                Ref("D5/L/Estimation/siegrist2026hypergeometric"), Text("; "), Ref("D5/L/Estimation/lecam1960poissonbinomial"), Text("; "), Ref("D5/L/Estimation/grinsteadsnell2006probability"), Text("."))
        )));

    private static DocumentBlock.Describe Theorem(string id, string name, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + name),
            H(name), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(ClassicalTools),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);
}
