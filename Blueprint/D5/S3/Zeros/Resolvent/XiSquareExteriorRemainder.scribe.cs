using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Resolvent;

internal sealed class XiSquareExteriorRemainderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual xi square source has its complete divisor and an entire exterior factor with a whole-plane square-mass remainder.",
        H("The Complete Xi Square Exterior Remainder"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("xi-square-cluster-exterior-remainder"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Resolvent/XiSquareExteriorRemainder.xi_square_cluster_exterior_remainder"),
                H("A complete actual divisor and exterior remainder"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let F(z) = xi(1/2 + i sqrt(z))/xi(1/2). Even square descent makes F entire "
                        + "and independent of the square-root branch. For every exhaustive ZeroData Z, "
                        + "rho_i = 1/2 + i gamma_i and the analytic order of F at gamma_i squared is "
                        + "the actual multiplicity m_i. Gamma can be complex; the theorem does not assume "
                        + "the Riemann hypothesis or simple zeros. The unconditional canonical ZeroData "
                        + "provider supplies an actual inhabitant of the source type.")),
                    Paragraph(Text(
                        "Select any finite set s of distinct zero indices. Retain one factor "
                        + "1 - z/gamma_i squared for every element of Fin(m_i) when Re(gamma_i) is positive; "
                        + "negative-height indices supply the identity. Q_s is the product of all selected "
                        + "multiplicity fibers, and A_s is the complete infinite product over the remaining "
                        + "positive-height fibers. The normalized resolvent, reflection pairing and entire "
                        + "identity theorem identify F with its full canonical product. Splitting that actual "
                        + "product proves F(z) = Q_s(z) A_s(z) for every complex z, while A_s is entire. "
                        + "No tail or finite exceptional set is omitted.")),
                    Paragraph(Text(
                        "At any complex a with A_s(a) nonzero, put M_s(a) equal to the complete sum of "
                        + "m_i divided by norm(a - gamma_i squared) squared over i outside s with "
                        + "positive real part of gamma. The exact drift-normalized exterior is "
                        + "g_a(w) = A_s(a+w)/A_s(a) times exp(-w A_s'(a)/A_s(a)). It is entire, "
                        + "and for every complex w its remainder norm(g_a(w)-1) is at most "
                        + "(exp(1/2)-1) times norm(w) squared times M_s(a) times "
                        + "exp(norm(w) squared times M_s(a)/2). This is a whole-plane estimate, "
                        + "including product zeros, rather than a small principal-log disk estimate.")),
                    Paragraph(Text(
                        "The reusable estimate uses E(u) = (1-u) exp(u). Its scalar norm and remainder "
                        + "bounds propagate through a finite product as the sharp invariant "
                        + "norm(product E(u_i)-1) at most (exp(1/2)-1) S exp(S/2), where S is the sum "
                        + "of norm(u_i) squared. Taking the limit over all finite subsets preserves the "
                        + "complete square-summable product. The recenter identity then uses exact infinite "
                        + "product division and the complete logarithmic-derivative sum, and sigma fibers "
                        + "recover the actual multiplicities in M_s(a). The finite sharp square-budget "
                        + "recurrence is the live new proof content; the analytic suppliers and actual-source "
                        + "bindings are used on that proof path. These are classical canonical-product "
                        + "estimates, with no claim of ordinary mathematical originality.")),
                    Paragraph(Text(
                        "An application of the same primary Gaussian bound gives the complete exterior "
                        + "derivative estimate. With the exact displacement function g_a(w) and the same "
                        + "complete multiplicity-weighted mass M_s(a) defined above, every complex w satisfies "
                        + "norm(g_a'(w)) at most exp(1/2) times norm(w) times M_s(a) times "
                        + "exp(norm(w) squared times M_s(a)/2). Differentiating E(w c_i) gives "
                        + "-w c_i squared exp(w c_i); the scalar Young inequality and the primary Gaussian "
                        + "bound put every finite-product derivative term under one common Gaussian "
                        + "majorant. Mathlib's finite-product derivative rule, norm triangle inequality "
                        + "and summation then give the finite square-mass bound. Locally uniform derivative "
                        + "convergence, the exact recenter identity and the sigma multiplicity fibers carry "
                        + "it to the full actual exterior. This complete application was checked by an "
                        + "exact Lean compilation and is recorded here as reuse, rather than a new derivative "
                        + "theorem. It assumes A_s(a) nonzero but requires neither RH nor a nonzero value "
                        + "of g_a at w, and includes every product zero. The two responses T_n(g_a') and "
                        + "(T_n g_a)' are distinct; this derivative estimate alone supplies neither response "
                        + "bound nor their commutation.")),
                    Paragraph(Text(
                        "The complete exterior also gives two distinct finite extraction derivative responses. Keep the same "
                        + "finite selection s, all actual exterior zero multiplicities and the infinite tail. Fix a complex "
                        + "center a with a nonzero and A_s(a) nonzero, and keep b_a = A_s'(a)/A_s(a) fixed. In absolute source "
                        + "coordinates put H_a(z) = A_s(z)/A_s(a) exp(-(z-a)b_a) = g_a(z-a). For a positive natural n, define "
                        + "the original falling-factorial extraction T_n h(z) = sum over j from 0 to n of h^(j)(0)/j! times "
                        + "n.descFactorial(j) times (z/n)^j. Set sigma = norm(a)/sqrt(n) and k = M_s(a) sigma squared. If k is "
                        + "less than one, the exact same source satisfies norm(T_n(H_a')(a)) at most 4 M_s(a) sigma/(1-k), and "
                        + "norm((T_n H_a)'(a)) at most 7 M_s(a) sigma / ((1-k) squared). This entire application, including the "
                        + "actual source and both responses in one statement, passed an exact Lean compilation; it introduces "
                        + "no new mathematical declaration.")),
                    Paragraph(Text(
                        "The reused Cauchy coefficient circle has kernel K_n(theta) = n!/(2 pi n^n) exp(n exp(i theta)-i n "
                        + "theta) on [-pi,pi]. The Stirling upper bound gives norm(K_n(theta)) at most e sqrt(n)/(2 pi) "
                        + "exp(-n(1-cos(theta))). At z = a exp(i theta), the displacement is w = a(exp(i theta)-1), with its "
                        + "exact squared norm equal to 2 norm(a) squared times (1-cos(theta)). This equality combines the "
                        + "kernel and complete-exterior Gaussian factors into exp(-n(1-k)(1-cos(theta))); only the polynomial "
                        + "prefactors use norm(exp(i theta)-1) at most abs(theta). Jordan's cosine bound then gives the common "
                        + "Gaussian exp(-2 n(1-k) theta squared/pi squared). Its first and third full-axis absolute moments are "
                        + "1/c and 1/c squared for c = 2 n(1-k)/pi squared. The exact constants e pi sqrt(e)/4 < 4 and e pi "
                        + "cubed (sqrt(e)-1)/8 < 7 supply the displayed bounds.")),
                    Paragraph(Text(
                        "For the second response the exact finite same-source recurrence, not derivative commutation, gives "
                        + "(T_n H_a)'(a) = n/a times the integral of K_n(theta)(1-exp(i theta))(H_a(a exp(i theta))-1). The "
                        + "constant and linear kernel moments remove the constant contribution. The normalization center and "
                        + "drift remain fixed throughout differentiation. Neither response bound assumes RH, a real spectrum, "
                        + "simple zeros or a finite-tail replacement. The application retains the local hypothesis k < 1; these "
                        + "two estimates alone do not prove every coupled node sign or RH.")),
                    Paragraph(Text(
                        "The same complete actual source also gives a finite extraction remainder and nonzero amplitude. With "
                        + "fixed a and b_a, the absolute-coordinate H_a above, n positive and k = M_s(a) norm(a) squared / n "
                        + "less than one, norm(T_n H_a(a)-1) is at most 3 k / ((1-k) sqrt(1-k)). This application allows a = 0. "
                        + "The constant kernel moment is exactly one; the complete exterior remainder, the exact combined "
                        + "circle Gaussian and the second Gaussian moment integral sqrt(pi)/(2 c sqrt(c)) supply the estimate. "
                        + "The numerical coefficient e (sqrt(e)-1) pi squared sqrt(pi)/(8 sqrt(2)) is less than three. If k is "
                        + "at most 1/16, the error is strictly less than 1/4, so norm(T_n H_a(a)) is greater than 3/4 and the "
                        + "amplitude is nonzero. The whole actual-source statement passed an exact Lean compilation with the "
                        + "standard axiom closure. This removes the extracted-amplitude nonzero premise under the stated local "
                        + "budget; it does not establish that budget uniformly over growing clusters or prove RH.")),
                    Paragraph(Text(
                        "The finite extraction also has exact fixed exponential tilt responses. For entire H, n positive and "
                        + "fixed complex b, put D(t) = 1 + b t/n. At any t with D(t) nonzero, T_n(exp(b z)H(z))(t) equals D(t) "
                        + "to the n times T_n H(t/D(t)); extracting the source derivative instead gives D(t) to the n times "
                        + "(T_n H'(t/D(t)) + b T_n H(t/D(t))). Differentiating the extraction gives D(t) to the n times "
                        + "((b/D(t)) T_n H(t/D(t)) + (T_n H)'(t/D(t)) / (D(t) squared)). The exact Cauchy coefficient identity "
                        + "and the constant dilation rule for iterated derivatives prove the first identity; the source product "
                        + "rule and differentiation of this fixed tilt prove the two distinct responses. The drift b remains "
                        + "fixed during differentiation.")),
                    Paragraph(Text(
                        "For the same actual A_s and H_a, write b = b_a, d = 1-a b/n nonzero and t = a/d. The source is "
                        + "exactly A_s(z) = C_a exp(b z) H_a(z), where C_a = A_s(a) exp(-a b) is nonzero. Then D(t) = 1/d and "
                        + "t/D(t) = a. Under a nonzero, n positive and k at most 1/16, the above small-mass result makes both "
                        + "T_n H_a(a) and T_n A_s(t) nonzero. The original-source responses s(t) = T_n A_s'(t)/T_n A_s(t) and "
                        + "ell(t) = (T_n A_s)'(t)/T_n A_s(t) satisfy exactly s(t) = b + T_n H_a'(a)/T_n H_a(a) and ell(t) = d b "
                        + "+ d squared (T_n H_a)'(a)/T_n H_a(a). Combining the already stated bounds with norm(T_n H_a(a)) "
                        + "greater than 3/4 gives norm(s(t)-b) at most 6 M_s(a) sigma and norm(ell(t)-d b) at most 11 norm(d) "
                        + "squared M_s(a) sigma. The exact source cancellation, complete actual source and both ratios and "
                        + "bounds passed one Lean compilation. These local conclusions retain A_s(a) nonzero, a nonzero, d "
                        + "nonzero and the small-mass budget. They do not discharge those hypotheses globally, growing-core "
                        + "node signs or RH.")),
                    Paragraph(Text(
                        "Under exactly the same local hypotheses, put chi(t) = t - (t squared/n) ell(t). The identities t - "
                        + "(t squared/n) d b = a and t d = a give chi(t)-a = -(a squared/n) (T_n H_a)'(a)/T_n H_a(a). "
                        + "Consequently norm(chi(t)-a) is at most 11 M_s(a) sigma cubed. The actual-source coordinate estimate "
                        + "was also checked by exact Lean compilation; it is local and supplies no global growing-core or "
                        + "all-critical premise.")),
                    Paragraph(Text(
                        "A local-removal application supplies a complete source mass on the height window used "
                        + "for growing cores. Let T be real with T at least 32 and let 0 < rho <= 1/8. From the "
                        + "actual exhaustive ZeroData, select exactly the positive-ordinate indices satisfying "
                        + "norm(gamma_i-T) <= 4 rho, with every original multiplicity. This is the filter of "
                        + "ZeroData.symmetricIndices(T+1) by those two conditions, so it is finite and omits no "
                        + "zero in the closed local neighborhood. Its total multiplicity is at most "
                        + "512 log(T+2). The complete unselected positive-ordinate sum of "
                        + "m_i/norm(gamma_i-T) squared is summable and at most "
                        + "(32+K) log(T+3)/rho squared, where K is the actual zetaZeroConfig.N(0,5). "
                        + "The local count supplier treats the near window; the unit-shell decomposition, "
                        + "logarithmic increment bound and inverse-square telescopes control every distant "
                        + "shell. No infinite tail is replaced by a finite numerical truncation.")),
                    Paragraph(Text(
                        "For every complex a with norm(a-T squared) <= 2 T rho, the same actual removal s "
                        + "satisfies M_s(a) <= (256+8K) log(T+2)/(T squared rho squared). The factorization "
                        + "gamma_i squared-T squared=(gamma_i-T)(gamma_i+T), positive real part of gamma_i "
                        + "and the source radius give norm(a-gamma_i squared) at least "
                        + "T norm(gamma_i-T)/2 for every exterior index. This transports the complete "
                        + "centered mass to the square-source mass with its original multiplicities. "
                        + "Neither this estimate nor the local selection assumes that the actual zeros "
                        + "lie on the critical line.")),
                    Paragraph(Text(
                        "The complete local exterior A_s is nonzero throughout that closed source region. "
                        + "The centered mass and actual local finiteness imply summability of the complete "
                        + "exterior reciprocal norms, including all sigma multiplicity fibers. The square "
                        + "separation makes every factor nonzero; Mathlib's "
                        + "tprod_one_add_ne_zero_of_summable then proves that the infinite product is "
                        + "nonzero, rather than inferring this from individual factors alone. Consequently "
                        + "the exact mass and nonzero conclusions can both be used by the earlier "
                        + "drift-normalized actual-source remainder and finite extraction applications. "
                        + "Their extraction-degree and fixed-tilt budgets still have to hold at the "
                        + "particular source or target being considered.")),
                    Paragraph(Text(
                        "The local divisor also has its literal polynomial normalization. Put "
                        + "Q(X)=product over i in s of (X-gamma_i squared) to the m_i and "
                        + "kappa=product over i in s of (-1/gamma_i squared) to the m_i. Then Q is a "
                        + "monic complex polynomial, its natural degree is exactly the sum of every "
                        + "selected original multiplicity, its degree is at most 512 log(T+2), and "
                        + "kappa is nonzero. Globally F(z)=kappa Q(z) A_s(z). The proof uses "
                        + "Polynomial.monic_X_sub_C, the monic product and power degree identities, "
                        + "and exact evaluation of the original cluster product. If every selected "
                        + "actual zero additionally has real part 1/2, the existing gamma-imaginary-part "
                        + "critical-line equivalence makes every gamma_i real. In that conditional case "
                        + "the same literal Q is a monic real polynomial whose mapped complex evaluation "
                        + "has the identical factorization and exact degree. The local all-critical "
                        + "premise is retained explicitly and has not been proved by this application.")),
                    Paragraph(Text(
                        "For any core subset of this complete local selection, keep every remaining "
                        + "selected factor in Q_far. The exact original source is F=Q_core A_hat, where "
                        + "A_hat=kappa Q_far A_s; no far selected multiplicity is discarded. Suppose d is "
                        + "positive and every far selected square zero has distance at least d from "
                        + "T squared. At a satisfying both norm(a-T squared) <= 2 T rho and "
                        + "norm(a-T squared) <= d/2, A_hat(a) is nonzero, and the full finite far-selected "
                        + "square mass is at most 2048 log(T+2)/d squared. The complete exterior mass "
                        + "above remains present alongside this finite contribution. The actual "
                        + "far-square gap is an explicit premise; a core label or the act of splitting "
                        + "the divisor does not supply it. These local mass, complete-product, monic "
                        + "normalization and retained-far applications passed exact Lean compilations "
                        + "with the standard axiom closure. They reuse the existing suppliers and add "
                        + "no new mathematical declaration or claim of ordinary mathematical novelty.")),
                    Paragraph(Text(
                        "A separate actual-xi application controls the complete local pole subtraction before "
                        + "square-coordinate transport. The existing general Landau disk supplier is used at "
                        + "radius 91/50 about 2+iT; its working radius (83/100)(91/50) covers the right "
                        + "half of the closed rho disc about 1/2+iT for rho <= 1/8. At absolute height at "
                        + "least six, the actual identity xi'/xi=1/s+1/(s-1)+GammaReal'/GammaReal+zeta'/zeta "
                        + "and the Gamma-side estimate bound the correction by C log(abs(T)+3). All "
                        + "Landau poles in its pole disc are original xi zeros with exactly the zeta "
                        + "analytic orders. The exact xi reflection transports both the logarithmic "
                        + "derivative sign and the original orders to the other closed half.")),
                    Paragraph(Text(
                        "At T >= 32 and 0 < rho <= 1/8, the complete local selection I maps "
                        + "bijectively under the actual zero enumeration onto every original xi zero "
                        + "in the closed 4 rho disc about 1/2+iT. Original analytic orders are the "
                        + "original multiplicities, and their full sum is at most 512 log(T+2). "
                        + "This complete set P need not equal a filter of the Landau poles. In the "
                        + "exact signed difference of the two finite pole sums, Landau poles outside "
                        + "P are separated from s by 3 rho, while P poles outside the Landau set "
                        + "are separated by 91/1000, the difference of its pole and working radii. "
                        + "The two full multiplicity bounds pay both contributions. Reflection "
                        + "transports the negative-height local divisor onto this same P, preserving "
                        + "every order and the signed pole sum on the other closed half. For one "
                        + "constant C > 0, every s in the closed rho disc "
                        + "with xi(s) nonzero therefore satisfies norm(xi'/xi(s)-sum over q in P "
                        + "of ord_xi(q)/(s-q)) <= C log(T+3)(1+1/(3 rho)). This application "
                        + "uses no local all-critical premise.")),
                    Paragraph(Text(
                        "The actual square source is entire and satisfies F(w squared) = "
                        + "xi(1/2+iw)/xi(1/2). Write E for the complete exterior of I. On the "
                        + "closed rho chart away from the original xi zeros, its literal "
                        + "monic-product logarithmic derivative split and the square chain rule give "
                        + "2w E'/E(w squared) = i[xi'/xi(1/2+iw)-sum over j in I of "
                        + "m_j/(1/2+iw-zero_j)]-sum over j in I of m_j/(w+gamma_j). "
                        + "The nonzero scalar normalization cancels exactly. "
                        + "Every retained partner w+gamma_j has norm at least T on the closed "
                        + "rho chart, so their complete sum has norm at most 512 log(T+2)/T; "
                        + "neither these partner factors nor any original multiplicity is omitted.")),
                    Paragraph(Text(
                        "On the closed w chart of radius rho/2, w squared lies in the already "
                        + "proved region where the complete E is nonzero. Its entire derivative "
                        + "therefore makes 2w E'/E(w squared) continuous there. Removing the finite "
                        + "complete original local zero set leaves a dense subset of the open "
                        + "chart, whose closure is the entire closed chart. The same norm bound "
                        + "extends by continuity, including the selected zero locations and the "
                        + "closed boundary. This extends the actual exterior function, without "
                        + "assigning a finite value to the original xi logarithmic derivative at "
                        + "a zero. For every z with norm(z-T squared) <= T rho/4, its principal "
                        + "square root w satisfies norm(w-T) <= rho/4 and norm(1/(2w)) <= 1/T. "
                        + "Consequently norm(E'/E(z)) <= B_E, where B_E = "
                        + "[C log(T+3)(1+1/(3 rho))+512 log(T+2)/T]/T, throughout that "
                        + "closed source disc, with no local criticality assumption.")),
                    Paragraph(Text(
                        "For any core subset of I, keep every far selected factor and write "
                        + "Ahat = kappa Qfar E and F = Qcore Ahat. Suppose each squared far "
                        + "zero is at least d > 0 from T squared, and 0 < r <= min(T rho/4,d/2). "
                        + "Then the actual complete Ahat is entire and nonzero on the closed r "
                        + "disc. Its logarithmic derivative is analytic there and has norm at most "
                        + "M = B_E + 1024 log(T+2)/d. The exterior term B_E is supplied by the "
                        + "preceding continued actual-source estimate. At every a with norm(a-T "
                        + "squared) <= r/2 and every integer n >= 0, the Cauchy estimate on the "
                        + "literal r/4 circle gives norm((d/dz)^n logDeriv(Ahat)(a)) <= "
                        + "n! M/(r/4)^n. All far powers, kappa and the complete infinite E remain "
                        + "in this same source; no finite-tail replacement is made.")),
                    Paragraph(Text(
                        "The complete-divisor, square transport, selected-zero continuation and "
                        + "retained-far source-jet applications passed one exact Lean compilation "
                        + "with the standard axiom closure. They reuse ZetaExplicit.Landau, "
                        + "VerticalLine, ZetaRvm.GammaSide, CompletedZeta, the actual zero "
                        + "enumeration, EntireEvenSquareDescent and the existing complete exterior "
                        + "theorem, together with Mathlib's finite-complement density and Cauchy "
                        + "derivative estimates. These are application consequences with no new "
                        + "mathematical declaration or ordinary novelty claim. The moving core's "
                        + "far gap d, real-source correspondence, original extraction coefficient "
                        + "budgets and full-growth complex spectrum remain separate obligations. "
                        + "No conclusion here establishes RH or strict Robin for every integer "
                        + "greater than 5040.")),
                    Paragraph(Text(
                        "The actual exterior also admits a full-height cutoff application of the existing rational "
                        + "fourth-moment tail. Let T be an integer at least five, and let the finite selected index set s "
                        + "contain ZeroData.symmetricIndices(T+1), so every actual zero in that spectral ball is selected "
                        + "with its original multiplicity. For any complex a with norm(a) at most (T+1) squared divided "
                        + "by two, every unselected gamma has norm(gamma) greater than T+1. The reverse triangle "
                        + "inequality gives norm(a-gamma squared) at least norm(gamma) squared divided by two. Each "
                        + "retained linear product factor differs from one by a quantity of norm at most one half and "
                        + "is nonzero. The existing exterior reciprocal norm summability and Mathlib's "
                        + "tprod_one_add_ne_zero_of_summable then make the complete exterior A_s(a) nonzero. This "
                        + "application derives the source nonzero condition under the stated cutoff and radius.")),
                    Paragraph(Text(
                        "Write R_T for rationalFourthMomentTail(T) in ExplicitWeilFourthMomentTail. Its exact "
                        + "fourthMomentSummand is multiplicity divided by (1+realPart(gamma) squared) squared. The "
                        + "outside-ball ordinate bound gives abs(realPart(gamma)) greater than T, so the complete "
                        + "exterior reciprocal-distance square summand is at most five times that fourthMomentSummand. "
                        + "Summing the positive-ordinate exterior indices under the proved complete two-sided "
                        + "multiplicity tail gives M_s(a) at most 5 R_T. The infinite exterior tail is retained; a factor "
                        + "four cannot be substituted with this supplier's exact units.")),
                    Paragraph(Text(
                        "Consequently, for n positive and 5 R_T norm(a) squared / n at most 1/16, the same actual "
                        + "absolute-coordinate H_a has norm(T_n H_a(a)-1) less than 1/4, norm(T_n H_a(a)) greater than "
                        + "3/4 and T_n H_a(a) nonzero. The combined complete actual-source statement passed an exact "
                        + "Lean compilation with the standard axiom closure and permits a=0. This full-height removal "
                        + "budget does not establish the local selected-degree C_0 log(T) budget from the growing-core "
                        + "theory, all-node signs or RH. Target-disc coverage additionally uses the degree condition below.")),
                    Paragraph(Text(
                        "A further application covers a whole closed target disc for the original extraction T_n A_s. "
                        + "Keep the same full-height cutoff, complete exterior and original multiplicities. Define C_s "
                        + "as the sum of the norms of exteriorReciprocal(Z,s,k) over every repeated exterior index k; "
                        + "the existing exterior reciprocal summability proves that this complete sum is finite. Let "
                        + "r be nonnegative and h positive, with r+2h at most (T+1) squared / 2. Assume n positive, "
                        + "2 C_s r(r+2h) less than n h, and 5 R_T (r+2h) squared / n at most 1/16. Then T_n A_s(t) "
                        + "is nonzero for every complex t with norm(t) at most r, including t=0.")),
                    Paragraph(Text(
                        "For nonzero t, use the closed rectangle centered at t with real and imaginary halfwidth h. "
                        + "Its points satisfy norm(a) at most r+2h, and its border satisfies norm(a-t) at least h. "
                        + "The full-height factor bound gives A_s(a) nonzero and norm(b_a) at most 2 C_s, where "
                        + "b_a=A_s'(a)/A_s(a). Apply the existing rectangle Rouche zero supplier from "
                        + "GermZeroCertificateReduction to the entire source-cleared function "
                        + "G_t(a)=(a-t)A_s(a)+(t a/n)A_s'(a), with reference (a-t)A_s(a). The degree inequality "
                        + "makes the perturbation strictly smaller on the border; the reference has just the simple "
                        + "zero t in this rectangle. At the supplied zero a, cancellation gives a=t d_a with "
                        + "d_a=1-a b_a/n. If d_a were zero then a would be zero, contradicting d_0=1. Thus d_a "
                        + "is nonzero at this preimage, and t nonzero also makes a nonzero. No denominator nonzero "
                        + "condition on the whole rectangle is assumed.")),
                    Paragraph(Text(
                        "The same full-height mass estimate gives M_s(a) norm(a) squared / n at most 1/16. The "
                        + "fixed-tilt identities and actual-source nonzero amplitude above therefore apply to this "
                        + "same a, n and A_s, giving T_n A_s(a/d_a) nonzero; a/d_a=t is the original target. At t=0, "
                        + "the extraction's constant coefficient is exactly A_s(0)=1. This complete target-coverage "
                        + "application was checked by exact Lean compilation with the standard axiom closure. It "
                        + "retains the infinite exterior and every original multiplicity throughout.")),
                    Paragraph(Text(
                        "For fixed T, s, r and h satisfying the cutoff and geometric clearance, the two degree "
                        + "budgets can also be discharged eventually. Choose a natural N greater than "
                        + "max(1,max(2 C_s r(r+2h)/h,80 R_T (r+2h) squared)). Every n at least N is positive and "
                        + "satisfies both budgets, so T_n A_s is nonzero on the entire closed target disc for every "
                        + "such n. This Archimedean application also passed exact Lean compilation. It gives a "
                        + "threshold for this fixed full-height exterior; it does not supply the local selected-degree "
                        + "C_0 log(T) core, a uniform growing-core threshold, coupled-node signs or RH.")),
                    Paragraph(Text(
                        "A conditional closed-disc Cauchy application controls both original-source responses. For "
                        + "entire functions H and V, positive D, and H nonzero throughout norm(z-c) at most D/8, write "
                        + "s(z)=V(z)/H(z) and ell(z)=H'(z)/H(z). Assume separately norm(s(z)) at most 16 S L/D and "
                        + "norm(ell(z)) at most 112 S L/D on that same closed outer disc, with S and L nonnegative. "
                        + "For every complex t with norm(t-c) at most D/16 and every m at least zero, the sum of their "
                        + "m-th derivative norms is at most m!16 to the m times 128 S L / D to the m+1. The closed "
                        + "circle about t of radius D/16 lies in the closed outer disc, including tangent boundary "
                        + "points. Entire H and V and the outer nonzero hypothesis give the quotients' differentiability "
                        + "and continuity on the inner circle and its interior. Applying Mathlib's "
                        + "Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le separately with the two budgets "
                        + "and adding gives the combined constant 128 S.")),
                    Paragraph(Text(
                        "The same conditional Cauchy application permits any positive circle radius R with "
                        + "dist(t,c)+R at most D/8: the joint m-th derivative norm is at most "
                        + "m! (128 S L/D) / R to the m. The complete closed circle and its interior lie in the "
                        + "closed outer disc, including equality in the containment condition. In particular, "
                        + "norm(t-c) at most D/10 permits R=D/40 and gives m!40 to the m times "
                        + "128 S L / D to the m+1; norm(t-c) at most D/12 permits R=D/24 and gives the "
                        + "corresponding factor 24 to the m. Both exact applications passed Lean compilation "
                        + "with the standard axiom closure and retain m=0. They reuse the two separate outer "
                        + "quotient budgets above, with their sum counted once.")),
                    Paragraph(Text(
                        "For the actual extraction, H=T_n A_s and V=T_n A_s' are entire polynomials. The preceding "
                        + "Cauchy conclusion is an exact compiled application of the pinned supplier, including m=0 "
                        + "and the entire inner closed boundary. It retains outer-disc nonzero and the two separate "
                        + "uniform quotient budgets as hypotheses. For a full-height exterior, the target-coverage "
                        + "application above supplies the nonzero hypothesis when its geometric and degree conditions "
                        + "hold on that outer disc. The required original-source uniform quotient budgets remain "
                        + "separate premises. This does not replace the local growing-core estimates.")),
                    Paragraph(Text(
                        "The general exterior remainder and transported-response results retain A_s(a) nonzero; the "
                        + "full-height application above derives it under its additional cutoff and radius conditions. "
                        + "The growing-multiplicity joint extraction budget and the signs of coupled Jensen responses "
                        + "for a nonempty Q_s remain separate mathematical obligations, as does the Riemann hypothesis."))),
                DescribeRole.Theorem))));
}
