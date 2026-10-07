using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.ContextUpdates;

internal sealed class CyclicSelectorRecoveryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cyclic selector boundaries give exact run positions and recover original group sources.",
        H("Cyclic Selector Recovery"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cyclic-selector-recovery"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/ContextUpdates/CyclicSelectorRecovery."
                    + "cyclic_selector_recovery"),
                H("Actual cyclic runs and labelled source recovery"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let m be even and at least two, r at least three, and f a fixed function "
                        + "from ZMod m to ZMod 2. Put G = ZMod 2 times ZMod m. A source contains "
                        + "a receiver a, r-1 labelled sender coordinates x_i, and a kernel offset "
                        + "h=(0,h_z). Its clock is t=a+sum_i x_i+h. The two selectors are "
                        + "tau_0=(1,0) and tau_1=(1,m/2). A sender replies with "
                        + "p_c(x)=x-chi(x)c, where chi is the binary first coordinate. "
                        + "The complete snapshot records a, t and every labelled reply.")),
                    Paragraph(
                        Text("The run geometry, labelled recovery, exact trace fibers and snapshot "
                            + "realization are supplied by "),
                        Ref("D5/S3/ObserverMemory/ContextUpdates/CyclicSelectorModel."
                            + "cyclic_selector_source_geometry"),
                        Text(". The cardinality argument constructs a surjective trace-class "
                            + "label on the original sources and proves its exact kernel before "
                            + "counting those classes.")),
                    Paragraph(Text(
                        "Every proposed snapshot (a,t,(u_i)) with replies u_i in H is realized "
                        + "by choosing binary bits with sum chi(t)-chi(a), setting "
                        + "x_i=u_i+epsilon_i c, and setting h=t-a-sum_i x_i. The parity equation "
                        + "puts h in H. Conversely every source producing that snapshot has exactly "
                        + "these bits and coordinates. This direct construction includes two senders. "
                        + "The statement describes every actual preimage without assuming source "
                        + "recovery from a single snapshot.")),
                    Paragraph(Text(
                        "At time j the receiver has translation (0,j), sender 2 has translation "
                        + "-(0,j), and the other senders and h are unchanged. The clock remains "
                        + "fixed. A trace of horizon n retains all snapshots at times zero through n. "
                        + "For two fixed sources with the same initial snapshot, their traces agree "
                        + "exactly when the sources are equal or f is constant on that entire phase "
                        + "window. A later return of the selector cannot remove an earlier trace difference.")),
                    Paragraph(Text(
                        "For nonconstant f, delta(z) is the least positive forward distance to a "
                        + "different label and beta(z) the corresponding backward distance. Actual "
                        + "run starts satisfy f(s-1) different from f(s). Every phase z has the unique "
                        + "start s=z-(beta(z)-1) and position k=beta(z)-1. Conversely a start and "
                        + "a position k less than delta(s) give the phase s+k. These inverse maps "
                        + "use cyclic addition throughout, including across phase zero. At that "
                        + "position delta(s+k)=delta(s)-k, with every delta between one and m-1.")),
                    Paragraph(Text(
                        "For nonconstant f and every nonnegative horizon n, the number of phases whose labels stay "
                        + "constant through times zero to n is the sum over actual starts s of "
                        + "max(delta(s)-n,0). The longest actual run has length L between one and "
                        + "m-1. Every phase has delta at most L, every depth from one through L "
                        + "is attained, and no constant window remains exactly when n is at least L. "
                        + "Length-one runs and the two-phase circle are included.")),
                    Paragraph(Text(
                        "Every actual snapshot fiber has q=2^(r-2) sources. At each fixed receiver "
                        + "phase there are C=4*m^r actual H-valued snapshots. A source-derived "
                        + "trace-class label retains its snapshot and, exactly when the selector "
                        + "window changes, its parity bitstring. The proved surjection and kernel "
                        + "identity give N_n=C*(q*m-(q-1)*A_n), where A_n counts constant windows. "
                        + "Thus N_0=4*m^(r+1) and the original source has 2^r*m^(r+1) elements. "
                        + "Ambient group-valued reply tuples are excluded from this image count.")),
                    Paragraph(Text(
                        "Two supplied observations at known times p and q from one original source "
                        + "recover every original coordinate when their selectors differ. Add the known "
                        + "time translation to sender 2's replies at each endpoint, subtract the "
                        + "normalized replies, and compare with zero to read each sender's binary "
                        + "coordinate. Reconstruct that sender from its first normalized reply and "
                        + "selector, undo the receiver translation, then subtract the receiver plus "
                        + "reconstructed sender sum from the clock to obtain h. The identity returns the original "
                        + "source and assumes a common source for both endpoints. The concrete "
                        + "arithmetic schedule normalizes both replies for each sender, subtracts "
                        + "them, compares with zero, reconstructs the coordinate, and adds it to "
                        + "the sum. It counts exactly 5*(r-1)+3 group operations and 3*(r-1)+1 "
                        + "comparisons, bounded by 5*r and 3*r. Two time-residue conversions and "
                        + "one public f evaluation are separate primitives. This ledger supplies "
                        + "no bit-time, acquisition, communication, or physical-time bound.")),
                    Paragraph(Text(
                        "At every phase, a source with zero senders and offset is distinct from "
                        + "the source obtained by flipping exactly senders 2 and 3 by the initial "
                        + "selector. They have the same initial snapshot, including when r=3. Their "
                        + "traces agree exactly on constant selector windows. On such a window the "
                        + "common snapshot at time j is computable from the initial snapshot by "
                        + "translating the receiver by (0,j) and sender 2's reply by -(0,j). "
                        + "For constant f this formula and the ambiguity persist at every time; "
                        + "no finite first-change boundary is assigned to the constant circle."))),
                DescribeRole.Theorem),
            new DocumentBlock.Section(H("Scalar profiles and actual run multiplicities"), Blocks(
            Paragraph(Text(
                "Keep the same actual model with even m at least two, r at least three, and "
                + "a public fixed function f:ZMod m to ZMod 2. Here G=ZMod 2 times ZMod m, "
                + "H={0} times ZMod m, and Source m r consists of a receiver a, the labelled "
                + "senders x_2 through x_r, and h in H. The clock is t=a+sum_i x_i+h, and "
                + "the snapshot uses c=tau_(f(z(a))) with the fixed selectors tau_0=(1,0) "
                + "and tau_1=(1,m/2). The only unit update adds (0,1) to a and subtracts it "
                + "from x_2. A horizon n trace contains n+1 snapshots, at every time from "
                + "zero through n, of the same updated source. Write R_n for equality of "
                + "these traces on the labelled source set and N_n for the number of its "
                + "equivalence classes. The run-profile conclusions below require f to be "
                + "nonconstant; a comparison selector g has the same domain and is also nonconstant.")),
            Paragraph(Text(
                "The run data are extracted from f on the actual cyclic carrier. RunStart f "
                + "consists of phases s with f(s-1) different from f(s), and delta_f(z) is "
                + "the least positive j for which f(z+j) differs from f(z). The length of "
                + "the run starting at s is delta_f(s). Let M_f be the multiset containing "
                + "one such length for each actual run start, with repetitions retained and "
                + "with colors and cyclic order forgotten. Every length lies between one "
                + "and m-1: a run contains its start, and nonconstancy supplies a different "
                + "color before a traversal of all m phases can be constant. Cyclic addition "
                + "also identifies runs that cross phase zero. These lengths are not an "
                + "independently supplied list.")),
            Paragraph(
                Text("Let A_n count phases z satisfying f(z+k)=f(z) for every integer k from "
                    + "zero through n. The actual run decomposition in "),
                Ref("D5/S3/ObserverMemory/ContextUpdates/CyclicSelectorModel."
                    + "cyclic_selector_source_geometry"),
                Text(" writes the phases in a run of length ell as s+k, with 0<=k<ell, "
                    + "and their first-change distances as ell-k. Thus a constant window "
                    + "requires n<ell-k, giving exactly max(ell-n,0) possible starting "
                    + "positions. Summing over actual runs gives A_n=sum_(ell in M_f) "
                    + "max(ell-n,0). In particular A_0=m, 0<=A_n<=m, and A_n=0 for "
                    + "every n at least the longest run L.")),
            Paragraph(
                Text("The exact actual-source counting formula in "),
                Ref("D5/S3/ObserverMemory/ContextUpdates/CyclicSelectorRecovery."
                    + "cyclic_selector_recovery"),
                Text(" is N_n=C*(q*m-(q-1)*A_n), where q=2^(r-2) and C=4*m^r. Since "
                    + "r>=3 gives q>1 and m>=2 gives C>0, both divisions in the rational "
                    + "inversion are legitimate: A_n=(q*m-N_n/C)/(q-1). All quantities "
                    + "in this inversion are regarded as rational numbers; the result is "
                    + "the integer window count. Its bound A_n<=m also ensures that the "
                    + "natural-number counting formula has no truncated subtraction before "
                    + "it is converted to this rational identity.")),
            Paragraph(Text(
                "For a single length ell define its clipped tail a_n=max(ell-n,0). "
                + "At each integer j>=1 it satisfies a_(j-1)+a_(j+1)=2*a_j+e_j, where "
                + "e_j is one if ell=j and zero otherwise. If ell<=j-1 all three tails "
                + "vanish; if ell=j they are 1,0,0; and if ell>=j+1 they are "
                + "ell-j+1, ell-j, ell-j-1, whose outer sum is twice the middle term. "
                + "This is the scalar second difference at the corner of the clipped tail.")),
            Paragraph(Text(
                "Sum that additive identity over M_f, counting repeated lengths separately. "
                + "The sum of e_j is exactly the multiplicity of length j, so "
                + "A_(j-1)+A_(j+1)=2*A_j+count_M_f(j). Equivalently, after converting the "
                + "A values to integers, count_M_f(j)=A_(j-1)-2*A_j+A_(j+1). The latter "
                + "subtractions are integer subtractions, not left-associated truncated "
                + "natural subtraction. For every 1<=j<=m-1 the inversion followed by "
                + "this identity recovers the actual length multiplicity. Lengths outside "
                + "that interval have multiplicity zero by the actual run bounds.")),
            Paragraph(Text(
                "Consequently, for nonconstant f and g with these same m and r, equality "
                + "of N_n for every nonnegative n is equivalent to M_f=M_g. Equal profiles "
                + "give equal A values by rational inversion and hence equal multiplicities "
                + "by the second difference. Conversely equal actual length multisets "
                + "give every A_n by the clipped-tail sum and then every N_n by the "
                + "counting formula. Even equality only for 0<=n<=m suffices: for each "
                + "admissible j, all of j-1,j,j+1 lie in this prefix, so it already "
                + "determines every multiplicity. Thus equality through horizon m is "
                + "equivalent to equality of the complete scalar profile.")))),
            new DocumentBlock.Section(H("An actual loss of cyclic order"), Blocks(
            Paragraph(Text(
                "Take m=10 and r=3 and write the selectors at phases zero through nine as "
                + "f_A=0110001111 and f_B=0111001111. Both are nonconstant functions on "
                + "ZMod 10. Their actual cyclic run starts are respectively 0,1,3,6 and "
                + "0,1,4,6. At those starts their first-change lengths are respectively "
                + "(1,2,3,4) and (1,3,2,4). In each word the last run has four ones at "
                + "phases six through nine and ends at the return to phase zero. Hence "
                + "the common uncolored multiset is {1,2,3,4}, although the orders differ.")),
            Paragraph(Text(
                "For both words the actual tail sum is max(1-n,0)+max(2-n,0) "
                + "+max(3-n,0)+max(4-n,0). Its values are "
                + "(A_0,A_1,A_2,A_3,A_4,...)=(10,6,3,1,0,...). Here q=2 and C=4000, "
                + "so N_n=4000*(20-A_n), giving "
                + "(N_0,N_1,N_2,N_3,N_4,...)=(40000,56000,68000,76000,80000,...). "
                + "For every n>=4 the window count stays zero and the trace-class count "
                + "stays 80000. These are the profiles of the stated actual words.")),
            Paragraph(Text(
                "Their difference persists after allowing any rotation, reflection, and "
                + "global complement. A rotation z to a+z or reflection z to a-z is a "
                + "bijection of ZMod 10; it transports each color fiber without changing "
                + "its cardinality. Complement exchanges the two color fibers. The "
                + "unordered color totals are therefore invariant under any composition "
                + "of these operations. They are {4,6} for f_A and {3,7} for f_B, "
                + "which are different. Thus no such operations identify these words, "
                + "even though their complete scalar profiles agree. This is an actual "
                + "example of lost cyclic order, with no claim that its length is minimal.")))),
            new DocumentBlock.Section(H("What phase and source labels retain"), Blocks(
            Paragraph(Text(
                "At every phase of a nonconstant selector, delta_f(z)=1 exactly when "
                + "f(z+1) differs from f(z): the least possible positive first-change "
                + "distance is one. Therefore phase-labelled delta values specify precisely "
                + "which actual edges z to z+1 are color boundaries. Choose f(0), then "
                + "propagate along the circle, flipping the binary value on each specified "
                + "boundary and retaining it on every other edge. This determines all "
                + "phase values once the initial bit is chosen.")),
            Paragraph(Text(
                "Equivalently, binary adjacent differences f(z+1)-f(z) in ZMod 2 are "
                + "one on boundary edges and zero on the others. If f and g have the same "
                + "phase-labelled deltas, their adjacent differences agree, so "
                + "g(z+1)-f(z+1)=g(z)-f(z). Every phase is reached by repeated addition "
                + "of one on the actual ZMod m carrier, hence g(z)=f(z)+b for the single "
                + "constant b=g(0)-f(0). The two possible values of b give equality or "
                + "one global complement; complement also preserves all first-change "
                + "distances. Wraparound is included: z+m=z and "
                + "f(z+n+m)=f(z+n). Since the boundary data come from an actual cyclic "
                + "function, propagation across the last edge returns to the chosen "
                + "initial bit. It introduces no independent choice at the cyclic seam.")),
            Paragraph(Text(
                "Now fix the source coordinates and the meanings of tau_0 and tau_1. "
                + "For every phase z consider the same two specified actual sources s_z "
                + "and s'_z. Both have receiver a=(0,z) and offset h=0. The first has "
                + "all senders zero; the second has x_2=x_3=tau_0 and all other senders "
                + "zero. The flips are always tau_0, independently of the observed f. "
                + "This is the actual zero-selector base-and-flip pair in the model. "
                + "There are two senders because r>=3. Since 2*tau_0=0, both sources "
                + "have sender sum zero, total coordinate sum Y=a, and clock t=a, while the sources themselves "
                + "are distinct because tau_0 is nonzero.")),
            Paragraph(Text(
                "If f(z)=0, the chosen selector is tau_0 and "
                + "p_(tau_0)(tau_0)=tau_0-tau_0=0, so every reply in both snapshots "
                + "is zero. If f(z)=1, the chosen selector is tau_1 and the second "
                + "source replies at senders 2 and 3 with "
                + "p_(tau_1)(tau_0)=tau_0-tau_1=Delta, where "
                + "Delta=tau_1-tau_0=(0,m/2). Here -Delta=Delta because 2*Delta=0, "
                + "and Delta is nonzero because even m>=2 gives 0<m/2<m. The first "
                + "source still replies with zero. The receiver and clock match in both "
                + "cases, so these reply differences decide equality of the complete snapshots.")),
            Paragraph(Text(
                "A horizon-zero trace consists of that one snapshot. Therefore "
                + "(s_z,s'_z) belongs to R_0 if and only if f(z)=0. Membership of these "
                + "fixed pairs in a given source-labelled R_0 determines every binary "
                + "value of f. In particular, if two selectors have equal R_0 relations "
                + "on these same source coordinates with the same tau labels, the zero "
                + "test agrees at every z and the selectors are equal. The conclusion "
                + "uses actual sources that exist in Source m r, and the identifying "
                + "pairs remain fixed when the selector being compared changes.")),
            Paragraph(Text(
                "A single saturated labelled relation has a different behavior. For both "
                + "actual words f_A and f_B the longest run is L=4, so at horizon four "
                + "no phase has a constant window. The trace-fiber result separates "
                + "every distinct pair with a common initial snapshot, and pairs with "
                + "different initial snapshots were already separated at time zero. "
                + "Thus R_4 for either word is exactly the diagonal {(s,s):s in Source 10 3} "
                + "on the same labelled source carrier. These relations coincide even "
                + "though f_A(3)=0 and f_B(3)=1. Their R_0 relations do distinguish the "
                + "selectors. Losing cyclic order by taking scalar class counts and "
                + "losing selector information in one saturated relation are distinct "
                + "phenomena; scalar-profile equality does not assert equality of all "
                + "source-labelled relations.")))),
            new DocumentBlock.Section(H("Whole windows and the limits of the data"), Blocks(
            Paragraph(Text(
                "The count A_n tests constancy at every phase in the window. It cannot "
                + "be replaced by the number of equal endpoints f(z+n)=f(z). In the "
                + "actual word f_A, take z=0 and n=3: f_A(0)=f_A(3)=0, but f_A(1)=1. "
                + "The intervening changes make this window nonconstant despite its "
                + "equal endpoints. Across all ten phases at horizon three, the "
                + "endpoint-equality count is four while the actual constant-window "
                + "count is A_3=1. Thus the clipped-tail statistic uses the whole "
                + "retained window rather than endpoint circular autocorrelation.")),
            Paragraph(Text(
                "These conclusions compare information contained in given public model "
                + "data: scalar trace-class profiles, depths with phase labels, and "
                + "relations with fixed source labels. The selector f is public from "
                + "the definition. Determination from a supplied relation does not grant "
                + "an observer queries to hidden sources or supply the entire relation "
                + "or profile for free from one source trajectory. No additional "
                + "acquisition ability, complexity bound, communication bound, or "
                + "physical-time claim follows here. The run-multiset characterization "
                + "is restricted to nonconstant selectors: a constant circle has no "
                + "actual first-change boundary and cannot be inserted as a finite run "
                + "of length m into these clipped-tail and multiplicity formulas.")))))));
}
