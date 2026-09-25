# A common complete-query law for all rooted triangles and nine old pair towers

Using the normalized kernels and conditional comparison already applied in [report561](561-all-three-rooted-supports-have-a-common-query-law.md), the following ordinary result holds. Let P={3,5,7,11,13,17,19}. Allow arbitrary pure prime-power originals, every rooted star 3^a q^b and every rooted triangle 3^a p^b q^c, and every non-3 pair tower p^b q^c for

    E9={(5,7),(5,11),(7,17),(7,19),(11,17),(11,19),
        (13,17),(13,19),(17,19)}.

Every displayed exponent is positive. The actual family is finite, all numerical moduli are distinct, and all phases are arbitrary and globally fixed. There is one supported law rho on the complete actual survivor with

    R_P(rho) <= 1904964287547135260286877282656943722389
                 /165993227993981410199733519903914391457
             =11.476156651500299... <566/49.

Arbitrary additional distinct originals touching23 or29, with arbitrary P-smooth cofactors, phases and finite heights, leave Haar survivor mass greater than1/20000. Restarting from this actual nine-coordinate Haar survivor also admits arbitrarily many additional primes strictly greater than2,000,000, with arbitrary tail-touching supports and a final positive distorted mass greater than1/50000. This is a support extension of the existing three-pair triangle class at the improved pure23/29 continuation target. It does not replace that class's stronger old query or Haar constants.

This is a normalized actual-law construction, not a two-phase-selector example. The gain is the complete-query certificate for a larger support class; no claim that its bare noncoverage range is new to the literature is made. No new Lean declaration or verification is claimed.

## Generic pair-graph interface

For any fixed graph E on Q=P\{3}, assign every actual mixed original to its largest prime q. Choose 0<=t_q<q-2 with Cq/q<=1, where Cq is defined below. Relative to the complete actual pure-q survivor, use precisely report561's normalized distortion kernel with parameter delta_q=t_q/(q-2). Its normalized rows and the actual original bad sets define one law mu. No auxiliary family is used as an actual input, and no phase is reselected for a query.

The full-past cylinder caps are

    C3=2, Cq=(q-1)/(q-2-t_q).

Write independent comparison heights Kp with Pr(Kp>=j)=Cp/p^j, j>=1, and gp=E Kp=Cp/(p-1). For each current exponent of q, the actual numerical cofactor labels are a subinventory of

    Mq=K3(1+sum_(5<=p<q)Kp)
           +sum_(p<q,(p,q) in E)Kp.                         (PG1)

The K3 term counts rooted stars; K3*Kp counts rooted triangles; the final terms count precisely the allowed non-3 pair towers. These inventories have distinct exponent-support patterns, so numerical labels are counted once. Different full original labels may retain different phases.

Apply conditional comparison before completing the auxiliary cofactor inventory. Report561's same normalized-kernel argument gives

    mu(Aq) <= bq=E(Mq-t_q)_+/(q-2-t_q),
    mu(U) >= s0=1-sum_q bq.                                (PG2)

Later normalized rows preserve previous event probabilities. The union bound uses these probabilities under the one mu; it does not assume that actual original events are independent.

For a fixed graph, the full mean is

    E Mq = g3(1+sum_(p<q,p>3)gp)
             +sum_(p<q,(p,q) in E)gp.                      (PG3)

The exact low atoms can be computed without cutting off a positive tail. At K3=0, only the neighboring Kp remain and every nonneighbor integrates to1. At K3=k>0, the low count is

    k+sum_(p<q,p>3)(k+1_((p,q) in E))Kp.                   (PG4)

Positive weights make every event Mq<t_q finite in its active coordinates. Weighted additive convolution computes those events exactly. The formula

    E(Mq-t_q)_+=E Mq-t_q+sum_(m<t_q)(t_q-m)Pr(Mq=m)       (PG5)

then retains all omitted heights through PG3. The same formula works at rational thresholds, using the integer values m<t_q.

## One schedule for the nine-edge graph

Use

|q|5|7|11|13|17|19|
|---|---:|---:|---:|---:|---:|---:|
|t_q|0|1|3|4|5|6|
|Cq|4/3|3/2|5/3|12/7|8/5|18/11|
|earlier neighbors|none|5|5|none|7,11,13|7,11,13,17|

Every cap satisfies 0<Cq/q<1. Exact PG5 charges are

    b5=1/3,
    b7=41/180,
    b11=920489/11907000,
    b13=50909297/1375258500,
    b17=90781256299136213353/2497678286228337712500,
    b19=268038946920165830699853032759/9236964773818146358478829093750.

Consequently

    beta=191596810431099913389001185664157
           /258635013666908098037407214625000,
    s0=67038203235808184648406028960843
         /258635013666908098037407214625000
      =0.2592000297459555... >0.                         (PG6)

The complete query includes every nonunit P-smooth numerical modulus, not only the original support patterns in PG1. Its auxiliary inventory is therefore

    V=product_(p in P)(1+Kp).

The full mean and exact low products below6 give

    B=E(V-6)_+
      =239287928554784833991367296504158
        /142550386045687261633715207859375
      =1.6786199967083448... .                           (PG7)

Let sigma=mu restricted to U and s=sigma(1)>=s0. For each finite query box, select its maximizing phases under this same sigma and include the unit cylinder. The pointwise bound L-1<=5+(L-6)_+, followed by mu's conditional comparison, gives

    integral (L-1) d sigma
      <=5s+integral 1_U (L-6)_+ d mu
      <=5s+integral (L-6)_+ d mu<=5s+B,
    R_P(sigma)<=5s+B.                                   (PG8)

Increasing finite boxes and the finite first moment give the complete all-height inequality. This does not carry a conditional cap through the final restriction. Dividing PG8 by s proves the displayed bound on rho=sigma/s.

The target is already positive before normalization:

    566s-49R_P(sigma) >=321s0-49B
      =202972318261283472997395138475101055867
        /213468632901872491547441988908582625000
      =0.9508297097428174... >0.                         (PG9)

The source density is at most

    Lambda=product_p Cp=2304/77.

Thus H(U)>=s0/Lambda=0.008662500994113965... .

## Arbitrary23/29 continuation with the same source

Use actual pure23 and pure29 survivor laws, whose positive-depth query sums are at most1/21 and1/27 and whose density product is at most616/567. Tensor them with sigma. The remaining originals touching exactly one fresh coordinate have total charge at most R_P(sigma)/21+R_P(sigma)/27; those touching both have charge at most [R_P(sigma)+s]/567. The unit old cofactor contributes s.

The surviving submeasure mass is at least PG9/567, and its density is at most Lambda*616/567. Therefore

    H(U_extended) >= PG9/(616 Lambda)
       =202972318261283472997395138475101055867
         /3934653841647313764202450739562994944000000
       =0.00005158581324559556... >1/20000.              (PG10)

This uses the actual pure-coordinate continuation in [report569, SD15–16](569-complete-suffix-debits-close-the-six-prime-query-target.md). All original supports touching23 or29 are allowed within the nine-prime carrier. This tensor step does not supply a query bound for the newly conditioned extended law. The large-prime continuation below instead restarts from actual restricted Haar.

The ordered-slot transport already proved in report561 Section7 also
applies here. Replace P by any seven ordered odd primes r0<...<r6,
use r0 as the root and transport E9 by slot. Keep the same thresholds.
At a later slot, C(r)=(r-1)/(r-2-t), its positive-depth tails C(r)/r^e
and the charge coefficient1/(r-2-t) decrease with r. At the root use
C(r0)=(r0-1)/(r0-2), with the same monotonicity. Independent uniform
couplings put each actual auxiliary height below its reference height.
Both PG1 and V are nondecreasing in every height, so the reference
beta, B and density product still bound this one construction. Two
distinct additional primes u>=23,v>=29 outside the carrier have the
same or smaller conditioned query sums and density factor. Thus the
same constants transport to these slots; this does not add head
coordinates or remove the graph restriction.

## Actual Haar restart and arbitrary primes above two million

This is a direct application of [report569, SD22–23](569-complete-suffix-debits-close-the-six-prime-query-target.md) and [Chapter33, SH5–SH13](../../problem-details/33-seven-small-primes-with-an-unrestricted-large-prime-tail.md), with the inherited Rosser--Schoenfeld prime-product premise. It changes neither the large-prime proof nor its ell=12 parameter.

Suppose every original prime belongs to P9={3,5,7,11,13,17,19,23,29} or is strictly greater than2,000,000. The P-supported originals retain the nine-edge shape condition above. Head originals touching23 or29 remain arbitrary. Every tail-touching original may have arbitrary head cofactors, other tail primes, finite heights and globally fixed phases, subject only to distinct full numerical moduli.

Resolve all head coordinates to the exponents used anywhere in the complete original family, including the tail-touching originals. Let U be the complete head-only survivor. Restart from the unnormalized measure

    nu0=H_P9 restricted to U.

Its mass is at least the PG10 head bound and hence greater than1/20000. Its joint density relative to head Haar is at most1. It is not the conditional probability H(.|U), and the earlier normalized-query cap is not transferred to it. Haar lifting to the enlarged finite head period preserves both this mass and the density bound.

The complete joint-load second moment is bounded by

    M2=product_(p in P9) p(p+1)/(p-1)^2=14003665/540672.

Chapter33's homogeneous transfer charges every tail original once, at its largest tail prime. At B=2,000,000 and ell=12, the source conditions B>=286, ell>=4, 3^ell<=B hold. With

    c=(2ell^2+1)/(2ell^2-1)=289/287,
    tau7(B,ell)=c^7/B * (B/(B-3))^2
                 *sum_(j=0)^7 7!/[(7-j)! ell^j],

the full tail loss is at most

    M2 tau7 =988643510345833942508989848828125
                /35490204709719259009199798947341533184
             =0.000027856799317787156... <3/100000.

It follows immediately that the final surviving distorted submeasure has mass

    >1/20000-3/100000=1/50000.

The exact coarse-head margin is0.000022143200682212843..., and using the full rational PG10 bound gives0.00002372901392780841.... Both are retained in the data. At the old cutoff1,000,000 the same tail-charge certificate exceeds the exact PG10 lower bound; this only shows that those two retained bounds do not certify that cutoff.

All normalized tail kernels preserve the entire previous joint measure, and the complete tail bad union is deleted only at the end. Thus the positive mass belongs to one actual complete survivor and yields an uncovered integer by finite CRT. The displayed number is distorted mass, not a final Haar-density lower bound or a final query bound. Extra support primes from31 through2,000,000 remain excluded. The exponent7 in tau7 comes from the transfer's prime-factor-growth estimate, not from counting the nine head coordinates.

## Scope comparison and remaining support gap

Report547's star result and the all-three-rooted theorem of Report561 do not contain the non-3 pairs here. Report561's triangle theorem allows old57, old1119 and old1719. All three edges remain in E9, together with six additional full pair towers. The old theorem's sharper numerical bounds remain valid for its smaller class; the new conclusion trades some numerical margin for a support extension without additional phase or height restrictions. Its extra additive allowance does not already give this uniform extension: under the old schedule the full511 and717 towers alone cost1/21+1/44=65/924>7/100; with its base beta>71/100 and B>3/2, the resulting estimate exceeds5+(3/2)/(22/100)=130/11>566/49. This compares those sufficient bounds, not all possible certificates for an individual actual family.

The new class has no shallow phase restriction. Thus it is not restricted to Report569's two-phase finite window. Conversely that window theorem admits arbitrary supports outside its finite restriction, so the two broader results have different scope.

The missing non-3 pairs are

    (5,13),(5,17),(5,19),(7,11),(7,13),(11,13).

Non-3 supports of three or more primes also remain outside PG1. Rooted supports containing three or more Q primes are outside this particular triangle class; Report561's alternative all-rooted theorem still applies when no non-3 mixed originals are present.

For the complete15-edge graph, the original schedule gives a best tested query threshold8 and bound15.4082816142.... The separate fixed schedule (0,1,3,5,7,8) gives bound13.3611275448..., still above566/49. These are failed sufficient estimates, not a lower bound on possible laws or an impossibility theorem for other schedules.

The nine-edge graph is one certified graph, not a maximum-edge or optimal graph claim. No exhaustive search of all32768 graphs was used or is claimed.

## Exact reproduction and remaining obligation

The standalone [evaluator](../../frontier/cover-geometry/rooted_triangle_pair_graph.py)
and [exact data](../../frontier/cover-geometry/rooted_triangle_pair_graph.json)
retain the final nine-edge certificate, the old three-edge comparison and
two fixed complete-graph diagnostics. Run the producer with standard-library
Python; its31 explicit checks remain active under optimization. An independent
direct enumeration of the low events and complete means passed179 exact
checks, including the earlier two-edge regression. The ordinary comparison
argument above carries the arbitrary-family and all-height quantifiers;
finite arithmetic does not establish them by enumeration.

The next missing input is a joint comparison strong enough for the omitted
supports on the SAME law. Adding per-support estimates from separately
chosen laws is not a valid completion. The method obstructions in
[report571](571-joint-residual-laws-retain-conditional-and-query-incidence.md)
show why changing the resolved conditionals or claiming automatic query
debits from mass loss cannot fill that gap without further hypotheses.
