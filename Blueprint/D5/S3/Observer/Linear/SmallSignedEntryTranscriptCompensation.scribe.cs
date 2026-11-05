using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class SmallSignedEntryTranscriptCompensationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Small signed entry compensation and exact acquisition", H("Small signed entry compensation and exact acquisition"), Blocks(
            Paragraph(Text("A native source s has positive finite order M, a rational symmetric tridiagonal matrix A, strictly positive adjacent links, and a distinguished first coordinate. For every real vector v, its quadratic form lies between one quarter and three quarters of the squared Euclidean norm. There is no common bound on order and no positive lower bound on links. An entry z is a rational vector. InBall(rho,z) means rho is nonnegative and the sum of the real squares of z is at most rho squared.")),
            Paragraph(Text("Commands are Read, Tick, Hold, and Add(u) for rational u. Read returns the current first coordinate. Tick replaces x by Ax and returns the new first coordinate. Add(u) replaces x by x+u e0 and returns a fixed acknowledgement; Hold leaves x unchanged and gives the same acknowledgement. The function run records every return in chronological order. The function finalState records the field after the whole word. The reference is the one-cell matrix [1/2] with zero entry.")),
            Describe.Lean(DescribeId.Create("small-signed-complete-transcript"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/SmallSignedEntryTranscriptCompensation.small_entry_complete_transcript_compensation"),
                H("One fixed small entry for a complete word"), StatementSource.FromAuthor(Compensation()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every positive rational radius and every finite command word, one fixed source and entry reproduce the reference's entire list of scalar returns and acknowledgements. Here t(w) counts actual Ticks, and S is the matrix of s. The witness has order t(w)+2, positive first link epsilon at most 1/8, diagonal 1/2, and all remaining links 1/8. The sum of absolute entry coordinates is strictly below the radius, hence so is the Euclidean norm.")),
                    Paragraph(Text("Normalize the weak first edge so that its upper entry is one and its lower entry is X. The root-return perturbation is divisible by X, while the observation pivots at distance j are the constant (1/8)^(j-1). Substitution X=epsilon squared converts the return perturbation into order epsilon squared and off-root observations into order epsilon. Solving the polynomial triangular system therefore gives z_i=epsilon W_i(epsilon squared). A coefficient bound and a rational choice of epsilon make this one entry arbitrarily small.")),
                    Paragraph(Text("The word demand is computed chronologically: each Add contributes its return discrepancy and each Tick shifts the remaining ages. Induction preserves every Read and every post-update Tick return, including repeated Adds at one epoch. Zero Ticks and zero compensating polynomials are included. A controller receiving these same returns makes the same local decisions and successful export."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("small-entry-deterministic-obstruction"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/SmallSignedEntryTranscriptCompensation.no_deterministic_exact_acquisition"),
                H("Deterministic exact acquisition is impossible at positive radius"), StatementSource.FromAuthor(Obstruction(false)),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("L and E are arbitrary local-state and export types. A controller p:L to Decision(L,E) can compute locally, call a native command and branch on its reply, or halt with an export. It has no source argument or source-dependent advice. AcquiresOnBall requires a finite successful execution on every admitted source and entry, and requires every successful export to satisfy the chosen target at its actual final field.")),
                    Paragraph(Text("The target is either exact native order, the entire impulse sequence (A^j)00, or the complete reply function of every finite legal continuation from the actual final field. Native order is a necessary component of exact native-law acquisition. A complete reply function is a necessary component of a self-sufficient stateful predictor, so these obstructions also exclude those stronger tasks. No effectiveness restriction or finite-state restriction is imposed on the local types.")),
                    Paragraph(Text("Replay a successful reference execution on the fixed compensating source. Its order differs and its second impulse moment differs. For the predictor target, compare the alternative continuations Tick;Tick and Add(1);Tick;Tick from each actual final field. The difference between their last scalars is the source's second moment. Both alternatives cannot agree across the two sources. These are alternative hypothetical continuations, with no reset or copying operation required."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("small-entry-fair-prefix-obstruction"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/SmallSignedEntryTranscriptCompensation.no_fair_zero_error_exact_acquisition"),
                H("Zero-error fair-bit acquisition is impossible"), StatementSource.FromAuthor(Obstruction(true)),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("A BitController additionally requests the next independent fair bit. A successful execution records its finite consumed bit prefix, finite command word, and export; arbitrary local computations between requests are allowed. The tape space is the infinite Bool product with its fair product measure. A tape belongs to finiteSuccess exactly when some successful finite execution uses a prefix of that tape. The event errorEvent additionally requires an incorrect export at the actual final field.")),
                    Paragraph(Text("FairAcquiresOnBall requires, separately on every fixed source and admitted entry, that the complement of finiteSuccess and the event errorEvent both have measure zero. Nontermination and unsuccessful runs are outside successful acquisition. Each fixed prefix cylinder has measure 2 to the negative prefix length, including mass one for the empty prefix.")),
                    Paragraph(Text("Almost-sure reference success supplies one successful finite execution. Its positive-mass cylinder and zero error force that fixed export to be correct on the reference. Construct one compensating source from its command word and then fix this source. The same bit prefix and replies replay the execution on this source, where the export cannot be correct. Its whole positive-mass cylinder is an error event. The construction gives no uniform positive lower bound on error independent of the controller, radius, or transcript."))), DescribeRole.Theorem))));

    private static Formula Compensation() => Disp(Seq(
        Forall, Sp, F.Id("rho"), InMacro, Sp, Mathbb, Grp(F.Id("Q")), Comma, Sp,
        F.Id("rho"), Gt, D(0), Comma, Sp, Forall, Sp, F.Id("w"), InMacro, Sp,
        App("List", F.Id("Command")), Comma, Sp,
        Exists, Sp, F.Id("epsilon"), Comma, Sp, F.Id("s"), Comma, Sp, F.Id("z"), Colon, Sp,
        D(0), Lt, F.Id("epsilon"), Le, Frac, Grp(D(1)), Grp(D(8)), Land, Sp,
        App("order", F.Id("s")), Eq, App("t", F.Id("w")), Plus, D(2), Land, Sp,
        App("InBall", F.Id("rho"), F.Id("z")), Land, Sp,
        Sum, Underscore, Grp(F.Id("i")), Abs(App("z", F.Id("i"))), Lt, F.Id("rho"), Land, Sp,
        App("run", F.Id("S"), F.Id("z"), F.Id("w")), Eq,
        App("run", F.Id("reference"), D(0), F.Id("w")), Land, Sp,
        Sub(Pow(F.Id("S"), D(2)), Seq(D(0), Comma, D(0))), Eq,
        Pow(Seq(Open, Frac, Grp(D(1)), Grp(D(2)), Close), D(2)), Plus,
        Pow(F.Id("epsilon"), D(2))));

    private static Formula Obstruction(bool fair) => Disp(Seq(
        Forall, Sp, F.Id("rho"), InMacro, Sp, Mathbb, Grp(F.Id("Q")), Comma, Sp,
        F.Id("rho"), Gt, D(0), Comma, Sp, Forall, Sp, F.Id("L"), Comma, Sp,
        F.Id("E"), Comma, Sp, Forall, Sp, F.Id("p"), InMacro, Sp,
        App(fair ? "BitController" : "Controller", F.Id("L"), F.Id("E")), Comma, Sp,
        Forall, Sp, F.Id("initial"), InMacro, Sp, F.Id("L"), Comma, Sp,
        Forall, Sp, F.Id("target"), InMacro, Sp, App("AcquisitionTarget", F.Id("E")), Comma, Sp,
        Neg, Sp, App(fair ? "FairAcquiresOnBall" : "AcquiresOnBall", F.Id("rho"), F.Id("p"),
            F.Id("initial"), F.Id("target"))));

    private static Formula App(string name, params Formula[] xs) => new Formula.Apply(F.Id(name), [.. xs]);
    private static Formula Pow(Formula x, Formula n) => Seq(x, Caret, Grp(n));
    private static Formula Sub(Formula x, Formula n) => Seq(x, Underscore, Grp(n));
    private static Formula Abs(Formula x) => Seq(Bar, x, Bar);
}
