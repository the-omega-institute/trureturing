using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class NativeRectangleEnvironmentDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Estimation/TimeArrow/NativeRectangleEnvironment.";
    private static readonly LibraryNoteRef[] ClassicalTools =
    [
        LibraryNoteRef.Create("D5/L/Estimation/siegrist2026hypergeometric"),
        LibraryNoteRef.Create("D5/L/Estimation/grinsteadsnell2006probability"),
        LibraryNoteRef.Create("D5/L/Estimation/lahirichatterjeemaiti2007hypergeometric"),
        LibraryNoteRef.Create("D5/L/Estimation/lecam1960poissonbinomial")
    ];

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The collapsed history and labelled outside counts determine both rectangle margins. The exact conditional law persists on the complete original observation space and yields explicit central-tail bounds.",
        H("Minimal and full native rectangle environments"),
        Blocks(
            Paragraph(Text("Use the native fiber, rectangle and original probability weights. nativeMinimalRectangleReadout retains the rectangle and the paired counts on every outside signal row, omitting both numeric margins. For a fixed representative z and natural k,l, write V=nativeRectangleRows S e o k l z, N=|V|, R=|{i in V: count e z.val i.val 1=k}|, U=|{i in V: count e z.val i.val (-1)=l}|, a(y)=nativeRectangleACount S e o k l y and Env={y in Fiber S e o: nativeMinimalRectangleReadout S e o k l y=nativeMinimalRectangleReadout S e o k l z}. These are the same objects in each native event formula below.")),
            Paragraph(Text("H N K n t is choose(K,t)*choose(N-K,n-t)/choose(N,n) when t<=n and is zero otherwise, using natural binomial coefficients cast to reals and real division. All natural differences use natural subtraction. A sum over range(n+1) includes t=0 through n. The cellCounts N R U t used for the real-valued geometric estimate is [t,U-t,R-t,N-R-U+t].")),
            Paragraph(Text("fullRectangleReadout S e k l x is the pair (collapsedObs S e x, nativeMinimalRectangleReadout S e x k l (x,rfl)). It retains the entire collapsed history, the rectangle and every outside signal-row count. It is defined on the complete original observation space rather than on a surrogate sample.")),
            Theorem("native-signal-count-totals", "NativeRectangleEnvironment.native_signal_count_totals",
                "For every natural M, q, s, support S : Support M q, experiment e in {pair,path} and complete history o : Obs M s e, with finite Sites s e, every y : Fiber S e o satisfies sum_{i in S} count e y.val i 1=|signedDepartureBlocks S e o 0| and sum_{i in S} count e y.val i (-1)=|signedDepartureBlocks S e o 1|."),
            Theorem("native-minimal-readout-eq-iff", "NativeRectangleEnvironment.native_minimal_readout_eq_iff",
                "For every natural M, q, s, support S : Support M q, experiment e in {pair,path} and complete history o : Obs M s e, with finite Sites s e, for every natural k,l and y,z : Fiber S e o, nativeMinimalRectangleReadout S e o k l y=nativeMinimalRectangleReadout S e o k l z if and only if nativeMarginRectangleReadout S e o k l y=nativeMarginRectangleReadout S e o k l z. The numeric margins are recovered from the same collapsed history and outside counts."),
            Theorem("native-minimal-four-cell-law", "NativeRectangleEnvironment.native_minimal_four_cell_law",
                "For every natural M, q, s, support S : Support M q, real r, experiment e in {pair,path} and complete history o : Obs M s e, with finite Sites s e, 1 <= q < M, 0 < r < 1 and 0 <= compensation M q r < 1, for every natural k,l,t and representative z : Fiber S e o, conditionalFiberMass S r e o (Env filtered by a(y)=t)/conditionalFiberMass S r e o Env equals choose(R,t)*choose(N-R,U-t)/choose(N,U) if t<=U, and equals zero otherwise. N,R,U,Env and a are those defined above from this z; the complete fiber has its induced finite enumeration."),
            Theorem("kernel-second-central-moment", "RectangleHypergeometricMoments.kernel_second_central_moment",
                "For every natural N,K,n with K<=N, n<=N and N>1, sum_{t=0}^n H N K n t*(t-n*K/N)^2 = n*(K/N)*(1-K/N)*((N-n)/(N-1)), with every quotient, subtraction outside binomial arguments and count cast in this formula taken in the reals.",
                AssessedProvenance.FromLiterature(ClassicalTools[0])),
            Theorem("kernel-central-tail", "RectangleHypergeometricMoments.kernel_central_tail",
                "For every natural N,K,n with K<=N, n<=N and N>1 and every real L>0, sum of H N K n t over 0<=t<=n with L*sqrt(N)<|t-n*K/N| is at most 1/(4*L^2). The threshold is strict.",
                AssessedProvenance.FromLiterature(ClassicalTools[0])),
            Theorem("native-kernel-event-mass", "RectangleHypergeometricMoments.native_kernel_event_mass",
                "For every natural M, q, s, support S : Support M q, real r, experiment e in {pair,path} and complete history o : Obs M s e, with finite Sites s e, 1 <= q < M, 0 < r < 1 and 0 <= compensation M q r < 1, for every natural k,l, representative z : Fiber S e o and decidable predicate P on the naturals, conditionalFiberMass S r e o (Env filtered by P(a(y)))/conditionalFiberMass S r e o Env = sum over t in range(U+1) satisfying P(t) of H N R U t. The complete fiber has its induced finite enumeration."),
            Theorem("native-minimal-central-tail", "RectangleHypergeometricMoments.native_minimal_central_tail",
                "For every natural M, q, s, support S : Support M q, real r, experiment e in {pair,path} and complete history o : Obs M s e, with finite Sites s e, 1 <= q < M, 0 < r < 1 and 0 <= compensation M q r < 1, for every natural k,l, representative z : Fiber S e o and real L>0, if N>1, then conditionalFiberMass S r e o (Env filtered by L*sqrt(N)<|a(y)-U*R/N|)/conditionalFiberMass S r e o Env <= 1/(4*L^2). All environment constants are taken from this same z, and the complete fiber has its induced finite enumeration."),
            Theorem("native-event-mass-le-kernel", "RectangleHypergeometricMoments.native_event_mass_le_kernel",
                "For every natural M, q, s, support S : Support M q, real r, experiment e in {pair,path} and complete history o : Obs M s e, with finite Sites s e, 1 <= q < M, 0 < r < 1 and 0 <= compensation M q r < 1, for every natural k,l, representative z : Fiber S e o, decidable predicate Q on Fiber S e o and decidable predicate P on the naturals, assume that for every y with the same minimal readout as z, Q(y) implies P(a(y)). Then conditionalFiberMass S r e o (Env filtered by Q)/conditionalFiberMass S r e o Env <= sum over t in range(U+1) satisfying P(t) of H N R U t. The complete fiber has its induced finite enumeration."),
            Theorem("central-four-cells-lower", "RectangleHypergeometricMoments.central_four_cells_lower",
                "For all real N,R,U,delta,t,w, assume N>0, delta>=0, delta*N<=R<=(1-delta)*N, delta*N<=U<=(1-delta)*N and |t-U*R/N|<=w. Then delta^2*N-w <= cellCounts N R U t j for every j : Fin 4. No integrality hypothesis is imposed."),
            Theorem("native-minimal-central-mass-tail", "NativeEnvironmentAnchors.native_minimal_central_mass_tail",
                "For every natural M, q, s, support S : Support M q, real r, experiment e in {pair,path} and complete history o : Obs M s e, with finite Sites s e, 1 <= q < M, 0 < r < 1 and 0 <= compensation M q r < 1, for every natural k,l and representative z : Fiber S e o with N>1, let C(y) be |a(y)-U(y)*R(y)/N(y)|<=2*sqrt(N(y)), using each y's own rectangle and margins. The sum of probability r e S y.val over y in the complete fiber with env(y)=env(z) and not C(y) is at most 1/16 times the sum of the same probability weights over env(y)=env(z). Here env is nativeMinimalRectangleReadout S e o k l; the complete fiber has its induced finite enumeration."),
            Theorem("full-native-four-cell-conditional-law", "NativeGlobalRectangleEnvironment.full_native_four_cell_conditional_law",
                "For every natural M, q, s, support S : Support M q, real r, experiment e in {pair,path} and complete history o : Obs M s e, with finite Sites s e, 1 <= q < M, 0 < r < 1 and 0 <= compensation M q r < 1, for every natural k,l,t, take z=(o,rfl) in Fiber S e o and its N,R,U. The sum over all original x : Obs M s e with fullRectangleReadout S e k l x=fullRectangleReadout S e k l o and nativeRectangleACount S e x k l (x,rfl)=t of probability r e S x, divided by the sum over all x with that full readout, equals choose(R,t)*choose(N-R,U-t)/choose(N,U) if t<=U and zero otherwise."),
            Theorem("full-native-conditional-mass-eq", "NativeGlobalRectangleEnvironment.full_native_conditional_mass_eq",
                "For every natural M,q,s, support S : Support M q, real r, experiment e, complete history o, natural k,l and arbitrary predicate P on Obs M s e, assume 1<=q<M, 0<r<1 and 0<=compensation M q r<1. The sum of probability r e S x over all original x with fullRectangleReadout S e k l x=fullRectangleReadout S e k l o and P(x), divided by the sum over that full-readout event, equals conditionalFiberMass S r e o of {y in Fiber S e o: nativeMinimalRectangleReadout S e o k l y=nativeMinimalRectangleReadout S e o k l (o,rfl) and P(y.val)}, divided by conditionalFiberMass S r e o of {y in Fiber S e o: nativeMinimalRectangleReadout S e o k l y=nativeMinimalRectangleReadout S e o k l (o,rfl)}. The induced finite fiber enumeration and classical decisions for P are used; no decidability hypothesis is added to the theorem."),
            Describe.Lean(DescribeId.Create("full-rectangle-readout"),
                DeclarationHandle.Create(Module + "fullRectangleReadout"),
                H("Full rectangle readout"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural M,q,s, support S : Support M q, experiment e, natural k,l and complete history x : Obs M s e, fullRectangleReadout S e k l x = (collapsedObs S e x, nativeMinimalRectangleReadout S e x k l (x,rfl))."))), DescribeRole.Definition),
            Paragraph(Text("Hypergeometric moments, Chebyshev tails and Poisson-binomial comparison are classical tools. Their finite formulas and the explicit formal consequences below are distinguished from the repo-derived identification of native conditioning events. No approximation theorem substitutes for that exact identification. See "),
                Ref("D5/L/Estimation/siegrist2026hypergeometric"), Text("; "), Ref("D5/L/Estimation/grinsteadsnell2006probability"), Text("; "), Ref("D5/L/Estimation/lahirichatterjeemaiti2007hypergeometric"), Text("; "), Ref("D5/L/Estimation/lecam1960poissonbinomial"), Text("."))
        )));

    private static DocumentBlock.Describe Theorem(string id, string name, string statement,
        AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + name[(name.LastIndexOf('.') + 1)..]),
            H(name), StatementSource.WithoutFormula(), provenance ?? AssessedProvenance.FromRepo(ClassicalTools),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);
}
