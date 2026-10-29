using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class RecursiveJointTranscriptDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Recursive refinement of complete typed source rows preserves every finite acquired adaptive transcript law.",
        H("Recursive joint residuals and adaptive transcripts"),
        Blocks(
            Paragraph(Text(
                "An interface specifies source states and observations at each type, parameterized actions between types, "
                + "and action-specific events, records and terminals. A source supplies its actual observation, legal domain, "
                + "normalized legal rows and a declared refusal event, terminal and record for every illegal attempt. "
                + "The total row uses the legal row on its legal domain and a point mass on that refusal triple elsewhere.")),
            Paragraph(Text(
                "The zero residual is equality of actual current observations. Each next residual retains the preceding "
                + "relation and compares legality and the entire joint row for every same-type action. Only successful "
                + "successors are replaced by their preceding residual classes. Events, records and individual typed "
                + "terminal identities are preserved. Taking the realized image of this output projection changes no equality "
                + "of joint rows: projection back to the output carrier recovers the usual quotient pushforward.")),
            Paragraph(Text(
                "A policy receives the remaining horizon, current interface observation, acquired archive and full ordered "
                + "history. Its selector returns a probability distribution on stopping or parameterized typed actions. "
                + "Selected actions satisfy its declared permission predicate. Archive updates may use the entire acquired "
                + "prefix and each new complete block of acquired tokens; "
                + "the selector has no source-state, quotient-class or probability-table argument. Source legality remains "
                + "part of the total row, so a permitted attempt can still produce an explicit source refusal.")),
            Paragraph(Text(
                "Execution appends the actual observation before selection. A selected action is recorded, then its "
                + "complete source row is sampled. The event and record are appended and written into the archive before "
                + "a successful successor continues. A fixed terminal ends execution and is recorded distinctly. "
                + "Stopping and exhaustion have separate tags. Thus run is an independently constructed probability mass "
                + "function on full ordered histories, rather than a supplied transcript-law table.")),
            Describe.Lean(
                DescribeId.Create("recursive-residual-preserves-adaptive-law"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/RecursiveJointTranscript."
                    + "recursive_residual_preserves_adaptive_law"),
                H("Recursive residuals preserve finite adaptive laws"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The interfaces, source, archive type, residual depth and smaller execution depth are arbitrary. "
                        + "The two initial states have the same interface type and recursive residual class. Initial "
                        + "archives and acquired prefixes match. The conclusion compares full probability mass functions, "
                        + "including every ordered correlation, for every policy with the declared acquired inputs.")),
                    Paragraph(Text(
                        "Induction anchors observations at depth zero. At the next depth the selectors receive equal "
                        + "observations and identical acquired inputs. For each selected action the induction hypothesis "
                        + "makes its full continuation law constant on the preceding successor classes, uniformly in "
                        + "the newly written archive. The realized-image factorization criterion factors this continuation "
                        + "through the joint output projection. Binding it against equal projected source rows proves the "
                        + "step, retaining event-record-successor correlations and each fixed terminal.")),
                    Paragraph(Ref(
                        "D5/S3/ConceptDynamics/RefinementFactorization/RealizedImageKernelFactorization."
                            + "realized_image_unique_factorization_iff_reverse_kernel"),
                        Text(" supplies the realized-image factor directly. The finite adaptive induction supplies the continuation invariance.")),
                    Paragraph(Text(
                        "All finite policies use the same typed action menu and interpreter. Finite prefixes are obtained "
                        + "by truncating execution; an acquired-history continuation uses that same interpreter after the "
                        + "prefix. The result therefore applies to every experiment in any declared family closed under "
                        + "these legal operations. No same-level lumpability is required. The discrete PMF argument also "
                        + "covers arbitrary finite or countable actual common sources, stochastic rows with zeros, "
                        + "multiple interfaces and actions, and unbounded acquired archive carriers.")),
                    Paragraph(Text(
                        "This is the positive implication from recursive joint residuals to finite transcript-law "
                        + "equivalence. It does not prove its converse, identify hidden states from equal observations, "
                        + "give an observer a full law table, establish one-run certification, or assert realization "
                        + "of every completion thread. Conditional identifiability, acquisition and physical claims "
                        + "require their separate contracts."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var t = F.Id("T"); var s = F.Id("S"); var ctype = F.Id("C");
        var n = F.Id("n"); var i = F.Id("i"); var z = F.Id("z"); var w = F.Id("w");
        var d = F.Id("d"); var p = F.Id("P"); var c = F.Id("c"); var h = F.Id("h");
        return Disp(Seq(
            Forall, Sp, t, Colon, Sp, F.Id("Interface"), Comma, Sp,
            s, Colon, Sp, Call("Source", t), Comma, Sp,
            ctype, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            n, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            i, Colon, Sp, Call("Ty", t), Comma, Sp,
            z, Comma, Sp, w, Colon, Sp, Call("State", t, i), Comma, Sp,
            Call("residual", s, n, i, z, w), Sp, Rightarrow, Sp,
            Forall, Sp, d, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            d, Sp, Leq, Sp, n, Sp, Rightarrow, Sp,
            Forall, Sp, p, Colon, Sp, Call("Policy", t, ctype), Comma, Sp,
            c, Colon, Sp, ctype, Comma, Sp,
            h, Colon, Sp, Call("List", Call("Token", t)), Comma, Sp,
            Call("run", s, p, d, i, z, c, h), Sp, Eq, Sp,
            Call("run", s, p, d, i, w, c, h)));
    }
}
