using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class FixedSupportIntegerActivationEnvelopeDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Robin/PriceRecord/FixedSupportIntegerActivationEnvelope.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed-support two-layer integer activation envelope.",
        H("A finite construction in the complete nonlinear integer image"),
        Blocks(
            Paragraph(Text(
                "The finite construction has passed native Lean elaboration and kernel "
                + "compilation. Scoped axiom and registration evidence are checked separately. "
                + "No freeze, independent review or RH conclusion is asserted. This is one "
                + "source implementation, not an independent review triplet. Local library "
                + "search found the probability, logarithm and finite-tail suppliers used below; "
                + "it did not locate a whole construction in the inspected scope. This is "
                + "neither universal absence nor a claim of literature novelty.")),
            Paragraph(Text(
                "Let S be any finite set of natural primes. The domain is all a:N->N "
                + "with a(p)>=1 for p in S, and no restriction on a(p) outside S. Its image "
                + "is exactly {OwnClockFixedSupport.phi(S,cast(a))-baseline(S)} over that "
                + "whole domain; C is the sInf of that image. No selected image, attained "
                + "minimum or near-minimizer is substituted. Put H=theta(S), L=log(H), "
                + "U=sum_S (a(p)-1)log(p), D=sum_S -log(1-p^(-(a(p)+1))), and "
                + "J_lambda=lambda*U+D. The original benefit, baseline and Euler constant "
                + "are retained. The consumed normalization is exactly "
                + "F=phi(S,cast(a))-baseline(S)=log(1+log(1+U/H)/L)+D. "
                + "Write A1=sum_S min(lambda*log(p),p^-2) and "
                + "A2=sum_S min(lambda*log(p),p^-3).")),
            Describe.Lean(
                DescribeId.Create("fixed-support-constructive-integer-trial-vector"),
                DeclarationHandle.Create(Prefix + "constructive_trial_vector"),
                H("Uniform ceiling, three, two and one construction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every finite prime support S, real lambda>0 and real q>=2 "
                        + "satisfying lambda*q^4<=1, the theorem constructs a supported-admissible "
                        + "a with J_lambda(a)<=A1+A2+lambda*q*(log(1/lambda)+1)+4/q^3. "
                        + "This primitive is independent of the own clock. Its literal trialVector "
                        + "is zero off S. At p in S with p<=q it is "
                        + "Nat.ceil(log(1/lambda)/log(p)); at p>q it is three when "
                        + "lambda*log(p)<=p^-3, two when p^-3<lambda*log(p)<=p^-2, "
                        + "and one otherwise. The equality at q and both activation equalities "
                        + "use these displayed active branches.")),
                    Paragraph(Text(
                        "The head proof derives lambda<=1/16 and T=log(1/lambda)>=4log(q). "
                        + "The public natural-ceiling bounds give a(p)>=4, "
                        + "(a(p)-1)log(p)<=T and p^(-(a(p)+1))<=lambda/p. The public "
                        + "Klartag.neg_log_one_sub_le gives D_p<=lambda. Thus J_p<=lambda*(T+1), "
                        + "and the two nonnegative minima may be added. Containment in "
                        + "Icc(1,Nat.floor(q)) gives head cardinality <=q. No new scalar "
                        + "ceiling or cardinality theorem is claimed as content.")),
                    Paragraph(Text(
                        "On the tail, put b=lambda*log(p). The choice three has local excess "
                        + "over min(b,p^-2)+min(b,p^-3) at most 2p^-4. The choice two has "
                        + "excess at most p^-6<=p^-4, and the choice one has excess at most "
                        + "p^-4-p^-3<=0. These use the same public logarithm bound. "
                        + "One finite_cubic_tail application to S filtered by p>q, with "
                        + "p^-4<=(1/q)p^-3, bounds the combined excess by 4/q^3. "
                        + "The uniform witness, admissibility and aggregate estimate form the "
                        + "new construction. The upper half of finite_integer_activation_envelope "
                        + "uses this estimate on its actual proof path."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fixed-support-full-integer-activation-envelope"),
                DeclarationHandle.Create(Prefix + "finite_integer_activation_envelope"),
                H("Exact finite free-r and free-q second-layer envelope"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For H=theta(S)>exp(1), L=log(H), lambda=1/(H*L), every real r,q "
                        + "with 0<r<=1, 2Lr<=1, q>=2 and lambda*q^4<=1 satisfies the finite "
                        + "bounds min(r,A1+A2-2lambda*log(1/lambda)-16Lr^2)<=C and "
                        + "C<=A1+A2+lambda*q*(log(1/lambda)+1)+4/q^3. "
                        + "There is no card(S)>=3 assumption: a support such as {65537} is "
                        + "not excluded by the statement. No RH, PNT, record, minimizer "
                        + "or prime-prefix premise is present.")),
                    Paragraph(Text(
                        "The lower proof is pointwise for every supported-admissible vector. "
                        + "At a prime put b=lambda*log(p), x=p^-2 and y=p^-3. The exponent "
                        + "cases one, two and at least three give J_p>=min(x,b+y,2b). "
                        + "Because x-y>=y, this minimum equals min(b,x-y)+min(b,y). Its "
                        + "shortfall from min(b,x)+min(b,y) is at most y on the strict "
                        + "correction set b>x-y, and is zero on the complementary set. "
                        + "This paid case/min calculation stays local in the consumer.")),
                    Paragraph(Text(
                        "Let X=1/lambda. The q hypotheses imply X>=16. For "
                        + "Q=sqrt(X/log(X)), the scalar logarithm and square-root identities "
                        + "give Q>1 and Q^2*log(Q)<=X/2. A correction prime has "
                        + "p^2*log(p)>X/2, since p>=2. The public "
                        + "EulerLayerRootSecondOrder.second_cutoff_strictMono forces p>Q. "
                        + "The public ActualPriceRecordPrimeStructure.finite_cubic_tail "
                        + "therefore gives total correction <=2/Q^2=2lambda*log(1/lambda). "
                        + "No private cutoff or logarithm owner is copied or exposed.")),
                    Paragraph(Text(
                        "The exact source normalization, global scalar defect and all-vector "
                        + "sublevel proof are adapted in this same owner. For u=U/H>=0,L>=1, "
                        + "the public rational logarithm bounds give 0<=log(1+log(1+u)/L)<=u/L "
                        + "and deficit <=u^2/L. If F<r, Real.abs_exp_sub_one_le is applied "
                        + "first at r and then at s=log(1+u), giving s<=2Lr<=1 and u<=4Lr. "
                        + "Both exponential divided-difference steps remain on the proof path. "
                        + "Thus F>=J_lambda-16Lr^2 in this branch; F>=r handles the other "
                        + "branch. No vector is discarded from the lower image.")),
                    Paragraph(Text(
                        "The all-one vector proves nonemptiness, and F>=0 proves boundedness "
                        + "below by zero. le_csInf transfers the pointwise lower minimum; "
                        + "csInf_le, membership of the constructed vector and F<=J_lambda "
                        + "transfer the upper estimate. These order and scalar helpers are "
                        + "consumed bindings, not separate claimed contributions. "
                        + "This source implements exactly depth K=3, not a parameterized "
                        + "finite-depth family or an infinite-depth lower theorem. It retains the exact quartic free-q condition. "
                        + "No optimized cutoff, cubic PNT tail, theta-PNT proof, asymptotic "
                        + "limit or freeze artifact is included. The mirrored Reg source audits "
                        + "the literal q observation in the head error with all hypotheses retained; "
                        + "its producer state is reported separately from kernel compilation."))),
                DescribeRole.Theorem))));
}
