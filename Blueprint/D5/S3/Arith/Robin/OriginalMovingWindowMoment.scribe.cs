using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class OriginalMovingWindowMomentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/OriginalMovingWindowMoment.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original Robin moving-window kernel supplies quantitative continuous moments and a complete source-faithful signed integral assembly.",
        H("The Original Moving-Window Moment"),
        Blocks(
            Paragraph(Text(
                "Use lambda(x)=1/(x log(x)) and the existing weight "
                + "w(x)=(log(x)+1)/(x^2 log(x)^2). The original window has "
                + "H(t)=t^(4/5), B(t)=t+H(t) and kernel "
                + "k(t,x)=(lambda(x)-lambda(B(t)))/(w(t)*t^(11/10)) "
                + "for t<x<=B(t), and zero elsewhere. In particular k(t,t)=0 "
                + "and k(t,B(t))=0. The price is evaluated only inside the "
                + "legal window; real powers are Real.rpow.")),
            Describe.Lean(
                DescribeId.Create("original-window-moment-estimate"),
                DeclarationHandle.Create(Prefix + "original_window_moment_estimate"),
                H("A quantitative continuous moment supplier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real t>=4 and beta>=0, define "
                        + "a_beta(t)=integral from t to B(t) of "
                        + "k(t,x)*(x-2)^(-beta). With "
                        + "C_beta=4+beta+2*beta*2^(beta+1), "
                        + "|a_beta(t)-t^(1/2-beta)/2| <= "
                        + "C_beta*t^(-1/5)*t^(1/2-beta)/2.")),
                    Paragraph(Text(
                        "The proof reuses ActualRobinClockCovariance.g, its "
                        + "original derivative and density-integral suppliers, "
                        + "MellinWeightedVariation.scaleWeight_antitone, and the "
                        + "weight_continuous lemma in LogarithmBounds. "
                        + "Their weight normalization gives "
                        + "w(B)*(B-x)<=lambda(x)-lambda(B)<=w(t)*(B-x). "
                        + "The logarithmic growth estimate proves "
                        + "(t/B)^4*w(t)<=w(B). Exact integration of these "
                        + "bounds gives the endpoint moment bounds "
                        + "(t/B)^4*(B-2)^(-beta)*H^2/(2*t^(11/10)) "
                        + "<=a_beta(t)<=(t-2)^(-beta)*H^2/(2*t^(11/10)). "
                        + "Negative-power derivative estimates and "
                        + "H^2/t^(11/10)=sqrt(t) supply the displayed error. "
                        + "A triangle enters only as a proved bound on the "
                        + "same price-difference kernel.")),
                    Paragraph(Text(
                        "The source definition is EL Definition 1.2 in "
                        + "FIBONACCI_ATOMIC_RELATION_GENERATION_ROBIN_SELECTED_EULER_LAYERS. "
                        + "The estimate applies separately to every point "
                        + "of any complete original S_X contained in [4,infinity), "
                        + "for example when ell_X>=4; it does not select, "
                        + "thin or displace that family. At beta=1/2 its "
                        + "continuous single-window main term is 1/2.")),
                    Paragraph(Text(
                        "This is a continuous kernel supplier. It proves no "
                        + "integral interchange for W_X, no absolute lattice "
                        + "error and no discrete critical-threshold theorem. "
                        + "It does not identify a geometric trajectory with "
                        + "the original maximizing integers or prove their "
                        + "cofinal existence. The initialized seven-divisibility "
                        + "guard has mean p_0+p_25, including Q=0; its testing "
                        + "error is not Lambda-1 or I_X. The proposed calibration "
                        + "s=x-3, mass-action flow, entropy and Fisher-action "
                        + "claims remain outside this theorem. The full signed "
                        + "Robin/RH obligation remains open."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "For a source-faithful application, take the OriginalWindow X "
                + "and OriginalBounds X ell R from OriginalFirstClockTransport, "
                + "with 256<=ell<R. Let S=selectedDomain X: the union of every "
                + "original good-edge interval, with overlaps counted once. "
                + "Its canonical sources are the least actual full-domain "
                + "maximizers over positive multiples of 5040p. Neither the "
                + "prime labels, the good-edge selector nor the integration "
                + "domain is replaced by an auxiliary probability law.")),
            Paragraph(Text(
                "Put J=floor(2R), alpha=151/500, D(t)=floor(t^alpha), "
                + "tau_d=d^(500/151), W(x)=integral_S k(t,x) dt, "
                + "Z_d(t)=sum_(1<=m<=floor(J/d)) log(m)k(t,dm), "
                + "and Y_d(t)=d^(-1)integral_t^B(t) log(x/d)k(t,x) dx. "
                + "The kernel support proves that Z_d equals the original "
                + "row with terminal floor(B(t)/d); added fixed-support terms "
                + "vanish. The complete von Mangoldt convolution gives "
                + "I=sum_(n<=J) Lambda(n)W(n)-integral W(x) dx. "
                + "The Chebyshev prime-power reindexing writes its sum as "
                + "J_prime+H_ref, where J_prime=sum_(prime p<=J)log(p)W(p) "
                + "and H_ref contains every exponent 2<=k<=floor(log(2R)/log(2)) "
                + "and every prime p<=(2R)^(1/k), with mass log(p)W(p^k). "
                + "All further terms vanish by the same original support.")),
            Paragraph(Text(
                "Use the full reference interval [ell,R] to define "
                + "K(x)=integral_[ell,R] k(t,x) dt, "
                + "r_d(x)=integral_([ell,R] intersect {t<tau_d}) k(t,x) dt/K(x), "
                + "P(t,x)=sum_(1<=d<=D(t)) mu(d)log(x/d)/d, and "
                + "Pbar(x)=integral_[ell,R] k(t,x)P(t,x) dt/K(x). "
                + "Both quotients use the real zero convention at K(x)=0. "
                + "The before-cut indicator is precisely 1_(t<tau_d); "
                + "the complementary early indicator includes t=tau_d.")),
            Paragraph(Text(
                "Define the frozen paired baseline directly by "
                + "B_pair=integral_S [sum_(d<=J) mu(d)sum_(m<=floor(J/d)) "
                + "log(m)k(t,dm)r_d(dm) "
                + "+integral_t^B(t) k(t,x)Pbar(x) dx-a(t)] dt. "
                + "Here a(t)=[log(log(B(t)))-log(log(t)) "
                + "-H(t)lambda(B(t))]/[w(t)t^(11/10)]. "
                + "This definition uses the actual frozen row and posterior; "
                + "it is not a residual defined by subtracting the other "
                + "terms from I.")),
            Paragraph(Text(
                "Let E_early(t)=sum_(d<=D(t))mu(d)[Z_d(t)-Y_d(t)]. "
                + "Let C_cut be integral_S of the full positive-pair sum "
                + "mu(d)log(m)k(t,dm)[1_(t<tau_d)-r_d(dm)], "
                + "and P_cut=integral_S integral_t^B(t) "
                + "k(t,x)[P(t,x)-Pbar(x)] dx dt. "
                + "Then exactly I=B_pair+integral_S E_early+C_cut+P_cut. "
                + "Indeed frozen rows plus C_cut restore all late lattice "
                + "rows, while the frozen posterior plus P_cut restore "
                + "all early continuous rows. Adding E_early restores "
                + "the missing early lattice rows, so the full finite "
                + "Mobius convolution remains unchanged.")),
            Paragraph(Text(
                "The interchange obligations are part of this application. "
                + "S is compact and lies in [ell,R]; the original joint "
                + "kernel is measurable, between zero and one there, "
                + "and supported in S times [0,2R]. Hence Fubini gives "
                + "integral W=integral_S a(t) dt, and the elementary "
                + "log-log primitive gives the displayed exact a(t). "
                + "Finite row sums, bounded logarithmic rows, the original "
                + "cutoff indicators and the posterior compensation pay "
                + "integrability of each integrated term. Initial atoms "
                + "t=x are excluded; terminal atoms x=B(t) have zero weight.")),
            Paragraph(Text(
                "For M=(volume S).toReal>0, the original paired strip "
                + "estimate on this same S gives "
                + "|I-B_pair-integral_S E_early| "
                + "<=6 M ell^(-99/500) log(2ell). This bounds the combined "
                + "cut correction. The early-row supplier separately bounds "
                + "the residual after subtracting boundaryHeight times "
                + "endpointSum; it does not yet bound the whole E_early.")),
            Paragraph(Text(
                "This application reuses Mathlib's "
                + "moebius_mul_log_eq_vonMangoldt and "
                + "Chebyshev.sum_PrimePow_eq_sum_sum. The detailed early-row "
                + "and paired-cut suppliers were consumed from project source "
                + "checkpoints bfd899aa4198fc3cd9a965d29ea85c61a9bca1a3 and "
                + "71ffdcd2c961011602d16a5c1b35ff0a027ea9e7. "
                + "The application creates no additional canonical Lean "
                + "theorem or claim that those separate suppliers are "
                + "declarations in this module. It supplies no favorable "
                + "signed lower bound for B_pair, no full early-boundary "
                + "cancellation and no cofinal positive-mass original "
                + "integer witnesses. The separate discrete and continuous "
                + "costs in the Robin upper estimates are unchanged.")),
            Paragraph(Text(
                "The original early supplier can also be consumed on this "
                + "same full S without discarding its signed initial endpoint. "
                + "Set b(t)=[lambda(t)-lambda(B(t))]/[w(t)t^(11/10)] and "
                + "Q_D(t)=sum_(1<=d<=D(t))mu(d)log(t/d)[fract(t/d)-1/2]. "
                + "The literal Bernoulli value at every integer is -1/2. "
                + "The endpoint body b(t)Q_D(t) is measurable and integrable "
                + "on S: its moving divisor sum extends exactly to the fixed "
                + "finite J by the original cutoff indicator, each smooth "
                + "coefficient is integrable on [ell,R], and the Bernoulli "
                + "factor is bounded by 1/2. No probability or polynomial "
                + "approximation replaces it.")),
            Paragraph(Text(
                "The exact early-row residual gives "
                + "|E_early(t)-b(t)Q_D(t)|<=t^(-62/125)log(t)/6. This "
                + "budget decreases for t>=256, so "
                + "|integral_S E_early-integral_S bQ_D| "
                + "<=M ell^(-62/125)log(ell)/6. Combined with the original "
                + "paired strip budget, |I-B_pair-integral_S bQ_D| "
                + "<=M delta(ell), where delta(ell)=6ell^(-99/500)log(2ell) "
                + "+ell^(-62/125)log(ell)/6. Thus "
                + "I>=B_pair+integral_S bQ_D-M delta(ell), preserving the "
                + "full original J_prime+H_ref and exact centering.")),
            Paragraph(Text(
                "This leaves a joint signed target, allowing cancellation "
                + "between the baseline and the actual endpoint term. For "
                + "the original fixed kappa<c_Q allowance with "
                + "c_Q=(sqrt(2)-1)/4, a sufficient remaining inequality is "
                + "B_pair+integral_S bQ_D>=-(kappa-delta(ell))M on the "
                + "cofinal actual positive-mass windows. The refinement "
                + "proves the residual budget only; that favorable joint "
                + "inequality and the cofinal witness obligation remain "
                + "open. It does not require I to be positive and introduces "
                + "no new canonical Lean declaration.")))));
}
