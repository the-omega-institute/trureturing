using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class AdaptiveMarkerFiniteLabelsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula seedType = F.Id("U");
        Formula policy = F.Id("p");
        Formula seed = F.Id("u");
        Formula word = F.Id("w");
        Formula labels = F.Id("z");
        Formula side = F.Id("s");
        Formula index = F.Id("i");
        Formula depth = F.Id("k");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula length = Call("length", word);
        Formula source = Call("completion", labels);
        Formula total = Call("sideTotal", word, side);
        Formula prefixState = Call("State",
            Call("reverse", Call("actions", word, depth)),
            Call("reverse", Call("replies", word, depth)),
            Call("decide", Seq(depth, Eq, length)));
        Formula finalState = Call("State",
            Call("reverse", Call("map", F.Id("fst"), word)),
            Call("reverse", Call("map", F.Id("snd"), word)), F.Id("true"));
        Formula finiteLabels = All(side, F.Id("Bool"),
            All(index, Call("Fin", Seq(total, Plus, D(1))),
                Seq(Call("endpoint", source, side, index), Eq,
                    Call("bit", labels, side, index))));
        Formula prefixes = All(depth, naturals,
            Seq(Open, depth, Leq, Sp, length, Close, Rightarrow,
                Call("actualRun", policy, seed, source, depth), Eq, prefixState));
        Formula conclusion = Seq(
            Begin, Grp(F.Id("gathered")),
            Call("noAdjacentOnes", source), Land, RowBreak, Grp(),
            Open, finiteLabels, Close, Land, RowBreak, Grp(),
            Open, prefixes, Close, Land, RowBreak, Grp(),
            Open, Call("actualRun", policy, seed, source, length), Eq, finalState, Close,
            Land, RowBreak, Grp(),
            Open, Call("actualQueryCount", policy, seed, source, length), Eq, length, Close,
            Land, RowBreak, Grp(),
            Open, Call("stoppingTime", policy, seed, source), Eq, length, Close,
            End, Grp(F.Id("gathered")));
        Formula statement = Disp(All(seedType, F.Id("Type"),
            Seq(OpenBracket, Call("MeasurableSpace", seedType), CloseBracket,
                Rightarrow,
                All(policy, Call("Policy", seedType),
                    All(seed, seedType,
                        All(word, F.Id("Word"),
                            Seq(Call("terminalFirstTrue", word), Rightarrow,
                                Call("policyConformity", policy, seed, word), Rightarrow,
                                All(labels, Call("Labels", word), conclusion))))))));

        Formula qL = F.Id("qL");
        Formula qR = F.Id("qR");
        Formula noise = F.Id("v");
        Formula interval = Seq(OpenBracket, D(0), Comma, D(1), CloseBracket);
        Formula record = Call("acquiredRecord", policy, seed,
            Call("originalSource", qL, qR, Call("fst", source), noise), length);
        Formula recordEquality = Seq(record, Eq, Open, seed, Comma, word, Close);
        Formula recordEvent = Seq(OpenBrace, noise, Colon, F.Id("Noise"), Mid,
            recordEquality, CloseBrace);
        Formula positiveFactors = All(side, F.Id("Bool"),
            Seq(Open, D(0), Lt, Call("Q", Call("if", side, qR, qL)), Close,
                Land, Open, D(0), Lt, D(1), Minus,
                Call("Q", Call("if", side, qR, qL)), Close));
        Formula originalConclusion = Seq(Begin, Grp(F.Id("gathered")),
            Open, positiveFactors, Close, Land, RowBreak, Grp(),
            Open, D(0), Lt, Call("noiseLaw", recordEvent), Close,
            Land, RowBreak, Grp(),
            Open, Exists, Sp, noise, Colon, F.Id("Noise"), Comma, Sp,
                recordEquality, Close, End, Grp(F.Id("gathered")));
        Formula originalStatement = Disp(All(seedType, F.Id("Type"),
            Seq(OpenBracket, Call("MeasurableSpace", seedType), CloseBracket, Rightarrow,
                All(policy, Call("Policy", seedType), All(seed, seedType,
                All(word, F.Id("Word"), Seq(Call("terminalFirstTrue", word), Rightarrow,
                Call("policyConformity", policy, seed, word), Rightarrow,
                All(labels, Call("Labels", word), All(qL, interval, All(qR, interval,
                Seq(Open, D(0), Lt, qL, Lt, D(1), Close, Rightarrow,
                    Open, D(0), Lt, qR, Lt, D(1), Close, Rightarrow,
                    originalConclusion)))))))))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Finite compatible two-arm labels realize a chronological stopped archive with its original seed.",
            H("Finite labels and causal acquired-prefix realization"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("finite-label-realization"),
                    DeclarationHandle.Create(
                        "D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerFiniteLabels.finite_label_realization"),
                    H("One supported completion realizes every prefix and the first stopping time"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Word is a chronological List of pairs of a Boolean arm and a Boolean reply. "
                            + "The archive consists only of the original seed u and this word w; "
                            + "it contains neither a root bit nor an infinite source. False selects "
                            + "the left arm and true selects the right arm. For every natural k, "
                            + "actions(w,k) and replies(w,k) map the corresponding projections over "
                            + "take(k,w). The policy receives their reversals, because actualRun "
                            + "stores acquired histories newest first.")),
                        Paragraph(Text(
                            "terminalFirstTrue(w) requires positive length T and, for each zero-based "
                            + "index k below T, reply k equal to decide(k+1=T). policyConformity(p,u,w) "
                            + "requires action k to equal the same policy p evaluated at the original "
                            + "seed u and the reversed prefixes before k. The seed space is an arbitrary "
                            + "Type with an arbitrary measurable-space instance. No probability law, "
                            + "standard Borel assumption, or additional seed observation is used.")),
                        Paragraph(Text(
                            "sideTotal(w,s) counts arm s in the whole action word, and occurrences(w,s,k) "
                            + "counts it in the prefix before k. A Labels(w) witness supplies, on each arm s, "
                            + "a Boolean label at every index from zero through sideTotal(w,s). The two "
                            + "labels at zero agree. Consecutive finite labels never both equal true. "
                            + "For every query k, its reply is exactly the 00 predicate of the labels at "
                            + "occurrences(w,s,k) and its successor, where s is that query's arm. "
                            + "Finite compatibility means that a Labels(w) witness exists; these auxiliary "
                            + "labels are witnesses of compatibility and are not additional archive fields. "
                            + "Their conditions contain no actualRun equation, source, execution witness, "
                            + "or inverse normal form.")),
                        Paragraph(Text(
                            "extended(z,s,i) keeps every supplied finite label and is false for i beyond "
                            + "sideTotal(w,s). completion(z) has the common label at index zero as root and arm s "
                            + "entry i equal to extended(z,s,i+1). The theorem holds for every Labels witness, "
                            + "using that single completion at all depths. Fin indices in the label-preservation "
                            + "clause are coerced to natural endpoint indices. The last equality coerces T "
                            + "to WithTop Nat. Thus it identifies the first stopping time, as well as "
                            + "the complete terminal state and the number of acquired queries.")),
                        Paragraph(Text(
                            "The causal induction reconstructs the state before each next policy choice. "
                            + "The reconstructed action and reply lists select the recorded arm, and its "
                            + "occurrence count selects the finite-label 00 response. Earlier prefixes "
                            + "remain active; the final prefix is stopped. The zero tail ensures global "
                            + "no-adjacent-ones support beyond both acquired arm lengths.")),
                        Paragraph(Text(
                            "This finite realization establishes a support-level component of the "
                            + "common-parameter stopped-archive construction. It does not assert root recovery, "
                            + "an inverse normal form, opportunity enumeration, positive Markov cylinder mass, "
                            + "likelihood or posterior formulas, almost-sure termination, or measurability "
                            + "of the archive maps. Those require separate results."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("finite-label-original-realization"),
                    DeclarationHandle.Create(
                        "D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerFiniteLabels.finite_label_original_realization"),
                    H("Strictly positive original-noise mass and a literal realization"),
                    StatementSource.FromAuthor(originalStatement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For every original seed space, policy p, fixed original seed u, chronological "
                            + "word w, terminalFirstTrue and policyConformity witnesses, every Labels(w) "
                            + "witness z, and every fixed pair qL,qR in the open square, all three conjuncts "
                            + "hold with that same pair and the same common label-root fst(completion(z)). "
                            + "The parameters may be distinct or equal. Q(q) is the extended nonnegative "
                            + "real image of q. Both Q(q) and 1-Q(q) are strictly positive on the open interval; "
                            + "the standard finite-product and natural-power positivity lemmas therefore "
                            + "give positivity of every finite product of these success and failure factors.")),
                        Paragraph(Text(
                            "Noise is the original carrier (Bool times positive naturals) to the closed "
                            + "unit interval. noiseLaw is its product of uniform interval volumes. "
                            + "For each arm, Z starts at the common root. At a true current bit its next bit "
                            + "is false; at a false current bit it is true exactly when that arm's next "
                            + "noise coordinate is strictly below its fixed parameter. originalSource "
                            + "retains the common root and these two outward Z tails. Noise coordinates "
                            + "at zero and one remain in the carrier. acquiredRecord is the original seed "
                            + "paired with the chronological reversal of the actual acquired action/reply zip.")),
                        Paragraph(Text(
                            "The causal finite-label theorem first derives the stopping time and actual "
                            + "record of completion(z). The source first-record equivalence then derives "
                            + "D(p,(u,T))=(u,w); this equation and the first-hit condition are conclusions "
                            + "of the proof, not hypotheses. Forbidden 11 and absence of an earlier 00 "
                            + "force alternation up to the last queried endpoint. The final 00 forces "
                            + "that endpoint to be false. The exact original-source first-record mass is "
                            + "therefore the product of two positive Q powers and the positive final "
                            + "1-Q factor. A positive measure set is nonempty, yielding an actual original "
                            + "noise realization for this same fixed seed, pair, root and word.")),
                        Paragraph(Text(
                            "The original-noise simulation proofs are a source-preserving adaptation of "
                            + "TauCeti/Probability/MarkovChain/Simulation.lean and "
                            + "TauCeti/Probability/Kernel/Randomization.lean at pinned revision "
                            + "da527980caecf7e72838e069c01f4a7e7633eca3. Their attribution and complete "
                            + "Apache-2.0 license are retained in the owning Lean source. The finite-label "
                            + "causal completion and its composition with the original record law are "
                            + "repository-derived. The imported Markov prefix-mass result remains its "
                            + "existing source of truth.")),
                        Paragraph(Text(
                            "For a legal finite canonical replay, terminalFirstTrue is precisely its "
                            + "nonempty final-only marker convention; policyConformity restricts its "
                            + "original-seed history-based choices. Each arm's freshly queried edges give "
                            + "the chronological occurrence counts. Restricting its compatible path labels "
                            + "through the two finite arm counts supplies Labels, including the common "
                            + "root, forbidden 11 and local 00 response. No execution, first-hit, decoder "
                            + "equality, terminal parity, positive singleton-seed mass, standard Borel seed, "
                            + "parameter prior, new observed root or independent auxiliary noise is assumed.")),
                        Paragraph(Text(
                            "This establishes the positivity and original-source realizability sentence "
                            + "for these finite inputs. It does not prove that every source produces a "
                            + "finite replay, nor the sibling opportunity or totality clause, full CPI7.2, "
                            + "inverse normal form, actual-rise counts, opportunity ranks, likelihood-density "
                            + "identification or prior integration."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("measurable-randomized-chain"),
                    DeclarationHandle.Create(
                        "D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerFiniteLabels.measurable_randomizedChain"),
                    H("Measurable recursive paths"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("Measurable", F.Id("g")), Land,
                        Call("Measurable", Call("uncurry", F.Id("f"))), Rightarrow,
                        Call("Measurable", Call("randomizedChain", F.Id("g"), F.Id("f")))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For arbitrary measurable spaces xi and alpha, g maps xi to alpha and f maps "
                            + "alpha times xi to alpha. randomizedChain starts at g(u(0)) and updates "
                            + "by f(previous,u(n+1)). The displayed hypotheses are precisely measurability "
                            + "of g and of the uncurried f. The conclusion is measurability into the "
                            + "whole countable product of states, so each finite coordinate is measurable.")),
                        Paragraph(Text(
                            "For the CPI.2 threshold recursion use xi = unitInterval times Bool times "
                            + "unitInterval, alpha = Bool, g(q,x,t)=x and f(b,(q,x,t))=step(q,b,t). "
                            + "The first map is a projection. The second is a Boolean measurable split "
                            + "and the measurable strict comparison t<q. For p=(q,x,v), let "
                            + "U(p)(j)=(q,x,v(kappa(j))), where kappa(0)=1 and kappa(n+1)=n+1 as "
                            + "positive naturals. Each coordinate of U is a product of projections and "
                            + "a fixed evaluation; measurable_pi_iff gives Measurable U. Composition "
                            + "with the displayed theorem yields joint path measurability. Unfolding "
                            + "randomizedChain and Z identifies their zero and successor branches; "
                            + "g ignores the dummy noise coordinate at zero. Applying the two literal "
                            + "arm projections and shifting each path by one gives joint measurability "
                            + "of originalSource in both parameters, the common root and all noise. "
                            + "Precomposition with a seed projection preserves this conclusion for an "
                            + "arbitrary measurable seed space. This is an application of the existing "
                            + "recursive-path theorem and introduces no new mathematical declaration."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("original-source-law"),
                    DeclarationHandle.Create(
                        "D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerFiniteLabels.originalSource_law"),
                    H("The original uniform noise realizes the two-arm law"),
                    StatementSource.FromAuthor(Disp(
                        All(F.Id("qL"), F.Id("unitInterval"),
                            All(F.Id("qR"), F.Id("unitInterval"),
                                All(F.Id("x"), F.Id("Bool"),
                                    Seq(Call("map", F.Id("noiseLaw"),
                                            Call("originalSource", F.Id("qL"), F.Id("qR"), F.Id("x"))),
                                        Eq, Call("reference", F.Id("qL"), F.Id("qR"), F.Id("x")))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For every fixed pair of closed-unit-interval parameters and every common "
                            + "Boolean root, noiseLaw pushed forward by originalSource is reference. "
                            + "reference is the product of armLaw(qL,x) and armLaw(qR,x), with both "
                            + "zero coordinates identified with the same fixed root and their outward "
                            + "tails placed on the two arms. Thus the equality supplies the full joint "
                            + "law, including independence at these fixed parameters and root; its "
                            + "finite restrictions follow by measurable pushforward. armLaw uses the "
                            + "transition sending true deterministically to false and false to true "
                            + "with probability q, exactly the CPI.1 matrix. Each parameter is held "
                            + "fixed throughout its arm. The theorem does not assert prior integration, "
                            + "a random-root mixture, seed independence or an integrated stopping law."))),
                    DescribeRole.Theorem))));
    }

    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, variable, Colon, type, Comma, Sp, body);
}
