using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Jensen;

internal sealed class NormalizedJensenDegreeLoweringDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed theta-moment Jensen polynomials satisfy exact degree lowering.",
        H("Normalized Jensen Degree Lowering"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("source-theta-kernel"),
                DeclarationHandle.Create(Prefix + "sourceThetaKernel"),
                H("Fixed even theta kernel"),
                StatementSource.FromAuthor(KernelFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "K denotes sourceThetaKernel. The natural index starts at zero, so n+1 "
                    + "runs over the positive integers. Absolute value specifies the even "
                    + "extension of the positive half-line expression. The primed sum denotes "
                    + "Lean's totalized tsum; this definition asserts no convergence theorem."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("source-theta-density"),
                DeclarationHandle.Create(Prefix + "sourceThetaDensity"),
                H("Fixed density expression"),
                StatementSource.FromAuthor(Disp(Seq(
                    Domain(Xx, Real()), Call(F.Id("p"), Xx), Eq,
                    Fraction(Call(F.Id("K"), Xx), Call(Re, XiCenter()))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "p denotes sourceThetaDensity, with the real part of the frozen xiReading "
                    + "at one half as its exact denominator. Private checked consequences of "
                    + "xi_reading_conj identify that real part with the complex central value "
                    + "and identify the complex coercion of p with K divided by that value. "
                    + "No nonzero-denominator or probability-mass theorem is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("source-theta-moment"),
                DeclarationHandle.Create(Prefix + "sourceThetaMoment"),
                H("Even density moments"),
                StatementSource.FromAuthor(Disp(Seq(
                    Domain(Kk, Natural()), Sub(F.Id("m"), Twice(Kk)), Eq,
                    Int, Underscore, Grp(Real()), Sp, Pow(Xx, Twice(Kk)), Sp,
                    Call(F.Id("p"), Xx), Thin, F.Id("d"), Xx))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "sourceThetaMoment(k) is m at index 2k. The integral is the real "
                    + "Lebesgue integral of x^(2k) times the displayed density. It uses Lean's "
                    + "totalized integral and does not assert integrability."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("source-theta-coefficient"),
                DeclarationHandle.Create(Prefix + "sourceThetaCoefficient"),
                H("Fixed moment coefficients"),
                StatementSource.FromAuthor(Disp(Seq(
                    Domain(Kk, Natural()), Sub(F.Id("a"), Kk), Eq,
                    Fraction(Sub(F.Id("m"), Twice(Kk)), Seq(Open, Twice(Kk), Close, Bang))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "a denotes the fixed sequence sourceThetaCoefficient. Its denominator "
                    + "is (2k)!, not k!. No Taylor-coefficient correspondence or assertion "
                    + "that a at zero is one is used."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normalized-jensen"),
                DeclarationHandle.Create(Prefix + "normalizedJensen"),
                H("Canonical Jensen adapter"),
                StatementSource.FromAuthor(AdapterFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "N(b,d) denotes normalizedJensen b d for any real coefficient sequence b. "
                    + "J is the frozen jensenPolynomial: its coefficients are choose(d,k) "
                    + "times gamma(n+k), for k from zero through d. Here gamma(k)=k!b(k), "
                    + "the shift is zero, and polynomial composition scales the variable "
                    + "by the real inverse of d. The final map is the coefficient embedding "
                    + "from real to complex polynomials. X is the polynomial indeterminate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("source-jensen-polynomial"),
                DeclarationHandle.Create(Prefix + "sourceJensenPolynomial"),
                H("Independent finite source polynomial"),
                StatementSource.FromAuthor(Disp(Seq(
                    Domain(Dd, Natural()), Sub(F.Id("P"), Dd), Eq, FallingSum(F.Id("a"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "P at index d denotes sourceJensenPolynomial d, defined independently "
                    + "by this finite sum in Complex[X]. descFactorial(d,k) is the natural "
                    + "falling factorial d(d-1)...(d-k+1), with value one at k=0; its "
                    + "quotient by d^k is the prescribed weight. Natural factors and real "
                    + "coefficients are coerced to Complex. The upper limit is exactly d."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normalized-jensen-falling-factorial"),
                DeclarationHandle.Create(Prefix + "normalizedJensen_eq_fallingFactorial_sum"),
                H("Exact canonical normalization"),
                StatementSource.FromAuthor(Disp(Seq(
                    GenericDomain(D(1)), N(Dd), Eq, FallingSum(F.Id("b"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every real sequence and every natural d at least one, the canonical "
                    + "adapter equals the finite falling-factorial sum. The proof distributes "
                    + "composition and coefficient mapping and uses the exact identity "
                    + "descFactorial(d,k)=k! choose(d,k)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normalized-jensen-degree-lowering"),
                DeclarationHandle.Create(Prefix + "normalizedJensen_degree_lowering"),
                H("Universal polynomial degree lowering"),
                StatementSource.FromAuthor(Disp(new Formula.Aligned([
                    GenericDomain(D(2)),
                    Seq(N(Dd), Minus, Fraction(D(1), Dd), Sp, F.Id("X"), Sp,
                        N(Dd), Apos, Eq, N(Previous()), Circ,
                        Open, Fraction(Previous(), Dd), Sp, F.Id("X"), Close)
                ]))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This is an equality of complex polynomials for every real sequence b. "
                    + "The prime denotes Polynomial.derivative and the circle denotes "
                    + "polynomial composition. Comparing coefficients reduces it to the "
                    + "falling-factorial recurrence, including the top index k=d and all "
                    + "indices beyond d. The degree bound makes both d and d-1 nonzero.")),
                    Paragraph(Text(
                    "For the literal xiSquareSource F, retain b(k)=Re(F^(k)(0))/k!, "
                    + "J_n=T_n F and G_n=T_n(F'). Actual xi conjugation, iterated through "
                    + "the total derivative-conjugation identity, makes every actual source "
                    + "jet real. Thus J_n is normalizedJensen b n and G_n uses the exact "
                    + "shifted coefficients b_prime(k)=(k+1)b(k+1). G_n extracts the source "
                    + "derivative and is distinct from the polynomial derivative J_n'. "
                    + "No theta-moment-to-xi-jet identity is assumed.")),
                    Paragraph(Text(
                    "For every n>=2 and complex t!=0, the complete finite recurrence gives "
                    + "J_(n+1)((n+1)t/n)=J_n(t)+(t/n)G_n(t) and "
                    + "J_n(t)-(t/n)J_n'(t)=J_(n-1)((n-1)t/n). Every top coefficient "
                    + "and every zero tail coefficient is included. At an actual J_n node, "
                    + "J_n'(t)G_n(t)=-(n/t)^2 J_(n-1)((n-1)t/n) J_(n+1)((n+1)t/n). "
                    + "At a positive real simple node, the preceding row is exactly "
                    + "-(t/n)J_n'. The next actual row's relative orientation remains "
                    + "unpaid; previous/current hyperbolicity does not by itself supply "
                    + "a favorable response sign.")),
                    Paragraph(Text(
                    "A same-source analytic application uses T_n f with coefficients "
                    + "((n)_k/n^k) f^(k)(0)/k!, for n nonzero and k from zero through n. "
                    + "For a complex smooth source preserving the real axis, derivative "
                    + "uniqueness identifies these complex jets with the embedded jets of "
                    + "its real restriction. The preceding canonical normalization theorem "
                    + "therefore identifies T_n f with normalizedJensen at that exact jet "
                    + "sequence. This identification does not assert that the fixed "
                    + "theta-density moments above already equal the jets of the actual xi source.")),
                    Paragraph(Text(
                    "The same coefficient recurrence gives T_n(zf) = t T_n f "
                    + "- (t^2/n)(T_n f)' and (T_n f)' = T_n(f') - (t/n)(T_n(f'))'. "
                    + "The top coefficient cancels in the second identity. Consequently, "
                    + "multiplication by z-a acts by L_a P = (t-a)P - (t^2/n)P'. "
                    + "Applying this exact operator twice extracts f(z) = "
                    + "(z-a_2)(z-a_1) Ahat(z), while source differentiation gives "
                    + "T_n(f') = L_a1 Hhat + L_a2(Hhat + L_a1 Vhat). Here "
                    + "Hhat = T_n Ahat and Vhat = T_n(Ahat'); the second response "
                    + "extracts the source derivative and is distinct from the derivative "
                    + "of the first response.")),
                    Paragraph(Text(
                    "For the original selection, regroup Q = Qfar Qcore and Ahat = A Qfar, "
                    + "with Qcore(z) = (z-a_1)(z-a_2). The far polynomial may have arbitrary "
                    + "degree and the real roots a_1 and a_2 may coincide, so both "
                    + "multiplicities remain present. The complete original source is "
                    + "f = A Qfar Qcore. Put J = T_n f, G = T_n(f'), H = T_n A and "
                    + "V = T_n(A'). On H nonzero, retain the original responses "
                    + "P = J/H and S = G/H - (V/H)P.")),
                    Paragraph(Text(
                    "On Hhat nonzero, set v = t^2/n, ell = Hhat'/Hhat, s = Vhat/Hhat, "
                    + "chi = t-v ell and eta = 1-v s'. These are derived from the same "
                    + "extracted source. With m = (a_1+a_2)/2, delta = (a_1-a_2)/2, "
                    + "x = chi-m and U = v chi', the exact core identities are "
                    + "p = x^2-delta^2-U, p' = 2x chi'-U' and w = 2 eta x-v eta'. "
                    + "Thus J = Hhat p and G = Hhat(s p+w).")),
                    Paragraph(Text(
                    "At a real actual node J(t)=0, assume H and Hhat nonzero, v>0, "
                    + "chi'>1/2, eta>1/2, |U'|<sqrt(v)/8 and |v eta'|<sqrt(v)/8. "
                    + "The node forces x^2 = delta^2+v chi' >= v/2. Both core responses "
                    + "have the sign of x and magnitude greater than 3|x|/4, which gives "
                    + "p'w > x^2/2 >= v/4. The exact original amplitude identity is "
                    + "H^2 P'S = J'G = Hhat^2 p'w, hence "
                    + "P'S > (1/4)(Hhat/H)^2 v. In the complex source application the "
                    + "same real-node product has zero imaginary part and positive real "
                    + "part; the node is simple.")),
                    Paragraph(Text(
                    "This conditional quadratic-core application uses the existing "
                    + "normalization, iterated derivative product rule, quotient rule and "
                    + "ordered-field estimates. It introduces no independent "
                    + "root-preservation or convolution theorem. Applying it to the "
                    + "actual xi source still requires its analytic factorization and jet "
                    + "correspondence, the local all-critical premise, exterior response "
                    + "estimates and central total multiplicity at most two. It does not "
                    + "establish arbitrary growing-core positivity, all-height exclusion, "
                    + "RH or strict Robin for every integer above 5040.")),
                    Paragraph(Text(
                    "The same-source application also treats a core of exactly three "
                    + "real source roots a_1,a_2,a_3, including repeated roots. Retain "
                    + "Ahat=A Qfar with no degree restriction on Qfar, and extract "
                    + "f=(z-a_3)(z-a_2)(z-a_1) Ahat. Three applications of L_a give "
                    + "J=L_a3 L_a2 L_a1 Hhat. Source differentiation gives "
                    + "G=L_a2 L_a1 Hhat+L_a3(L_a1 Hhat+L_a2(Hhat+L_a1 Vhat)); "
                    + "it is the extraction of f', with the same exterior and far factor.")),
                    Paragraph(Text(
                    "Put m=(a_1+a_2+a_3)/3, beta_i=a_i-m, "
                    + "a=sum(beta_i^2)/6 and b=beta_1 beta_2 beta_3. The real-source "
                    + "discriminant gives a>=0 and |b|<=2a sqrt(a), even when roots "
                    + "coincide. Set x=chi-m, U=v chi', V_3=v U', "
                    + "Z_3=v(v eta')' and M_3=3(x^2-a-U). Quotient and product "
                    + "differentiation of the actual Hhat,Vhat yields "
                    + "p_3=x^3-3(a+U)x-b+V_3, "
                    + "p_3'=chi' M_3-3U' x+V_3' and "
                    + "w_3=eta M_3-3v eta' x+Z_3. Thus "
                    + "J=Hhat p_3 and G=Hhat(s p_3+w_3). Both V_3 and Z_3 "
                    + "retain the noncommuting derivative terms.")),
                    Paragraph(Text(
                    "For a>=0, u>0, |b|<=2a sqrt(a) and |e|<=u sqrt(u), an "
                    + "actual real root x of C(z)=z^3-3(a+u)z-b+e satisfies "
                    + "|C'(x)|>=(3/2)sqrt(u)(|x|+sqrt(a+u))>=(3/2)u. "
                    + "Indeed, with h=sqrt(a+u) and y=|x|, the source bounds give "
                    + "|b-e|<=2h^3-u h. The root equation forces y<2h and "
                    + "(y-h)^2(y+2h)>=u h, hence |y-h|>=sqrt(u)/2. "
                    + "Factoring |C'(x)|=3|y-h|(y+h) gives the stated margin. "
                    + "This pointwise comparison does not assume the roots have "
                    + "already been labeled or analytically continued.")),
                    Paragraph(Text(
                    "At an actual real J-node, assume H and Hhat nonzero, v>0, "
                    + "sigma>0, |U-sigma^2|<sigma^2/32, |V_3|<sigma^3/32, "
                    + "|chi'-1|<1/64 and |eta-1|<=1/128. Also assume "
                    + "|U'|<sigma/256, |V_3'|<sigma^2/256, "
                    + "|v eta'|<sigma/256 and |Z_3|<sigma^2/256. Applying the "
                    + "cubic slope bound at u=U,e=V_3 yields "
                    + "sigma |x|<=|M_3| and sigma^2<2|M_3|. Each response "
                    + "correction has magnitude below 5|M_3|/256. Consequently "
                    + "p_3'/M_3 and w_3/M_3 exceed 1/2, and "
                    + "p_3'w_3>M_3^2/4>v^2/4. The original identity "
                    + "H^2 P'S=J'G=Hhat^2 p_3'w_3 therefore gives "
                    + "P'S>(1/4)(Hhat/H)^2 v^2>0.")),
                    Paragraph(Text(
                    "This cubic real-node application remains conditional on the "
                    + "complete exterior jet estimates, actual xi factorization and "
                    + "jet correspondence, the local all-critical premise and central "
                    + "total multiplicity exactly three. It does not prove moving "
                    + "complex-root branches, target-disc node counts, endpoint "
                    + "existence criteria or uniform growing-core control. Those "
                    + "interfaces, all-height exclusion, RH and strict Robin above "
                    + "5040 remain unresolved by this application.")),
                    Paragraph(Text(
                    "For the fixed reference cubic Cstar(z)=z^3-3(a+sigma^2)z-b, "
                    + "assume a>=0, sigma>0 and |b|<=2a sqrt(a). Writing "
                    + "h=sqrt(a+sigma^2), the endpoint signs and the intermediate "
                    + "value theorem construct roots in (-2h,-h), (-h,h) and "
                    + "(h,2h). The preceding slope comparison gives distance at "
                    + "least sigma/2 from either adjacent critical point, hence "
                    + "both adjacent reference-root gaps are at least sigma. "
                    + "No root labels are imposed as hypotheses.")),
                    Paragraph(Text(
                    "For each fixed complex U and V_3 with "
                    + "|U-sigma^2|<sigma^2/32 and |V_3|<sigma^3/32, compare "
                    + "C(z)=z^3-3(a+U)z-b+V_3 with Cstar on the fixed square "
                    + "around each reference root, of halfwidth sigma/12. "
                    + "The square lies strictly inside the sigma/8 disc, and "
                    + "its border is at distance at least sigma/12 from the "
                    + "center. Factoring Cstar and using the reference slope "
                    + "gives the border lower bound "
                    + "(147/1536)sigma^2(|lambda|+h), strictly exceeding the "
                    + "original perturbation budget (3/32)sigma^2(|lambda|+h). "
                    + "The existing rectangle Rouche zero-count supplier "
                    + "therefore gives one unique simple C-zero in each square.")),
                    Paragraph(Text(
                    "These three zeros are distinct and satisfy "
                    + "|s_j-lambda_j|<sigma/8. Their actual root equations imply "
                    + "the complete identity C(z)=(z-s_1)(z-s_2)(z-s_3) at "
                    + "every complex z. This is a pointwise construction for "
                    + "every allowed pair U,V_3; neither the zeros nor the "
                    + "factorization are assumed. It reuses the same scalar "
                    + "comparison and existing complex analytic zero count.")),
                    Paragraph(Text(
                    "For real selected a,b,c, let Ahat(z)=B(z)Qfar(z), F(z)=(z-c)(z-b)(z-a)Ahat(z), H=T_n Ahat, "
                    + "Vhat=T_n Ahat', J=T_n F, and G=T_n F'. Here n is nonzero, Qfar is an arbitrary complex "
                    + "polynomial and B is supplied ContDiff over C. These are the actual complete sources of the "
                    + "finite extraction, not independently chosen responses. At each H(t)!=0 the checked "
                    + "polynomial identities give J=H P, J'=H' P+H P1 and G=H(S P+W), with all rational jets "
                    + "taken from this same H,Vhat. The checked jet identities and the open H!=0 neighborhood "
                    + "prove that the actual chi,U,V3,eta are analytic at t.")),
                    Paragraph(Text(
                    "The sigma/12 fixed-box unique roots glue through local implicit uniqueness to three labels "
                    + "lambda_j of the same cubic for every good complex parameter. The original amplitude "
                    + "budgets |U-sigma^2|<sigma^2/32 and |V3|<sigma^3/32 imply |lambda_j-l_j|<sigma/8 and exact "
                    + "cubic factorization for every complex z. Reference gaps and moving gaps give "
                    + "|lambda'_j|<1/54<1/32 from |U'|<sigma/256 and |V3'|<sigma^2/256; no separate derivative "
                    + "margin is assumed. Actual U,V3 conjugation identities imply conjugation of these same "
                    + "constructed labels.")),
                    Paragraph(Text(
                    "For a convex conjugation-invariant complex set S, retain H!=0, the original amplitude and "
                    + "derivative budgets, |chi'-1|<1/64 and the actual-source conjugation identities throughout "
                    + "S. The actually constructed coordinate branches f_j=chi-m-lambda_j are analytic and "
                    + "injective on the whole S, including its boundary. Each branch node is real and simple, and "
                    + "distinct branches share no node. The complete extraction satisfies "
                    + "J(t)=H(t)f1(t)f2(t)f3(t) on S. Consequently its actual J zero set on S is finite, all its "
                    + "zeros are real and simple and its cardinality is at most three. Finiteness and this count are "
                    + "conclusions from the three injective branches, not premises.")),
                    Paragraph(Text(
                    "At each t in S, analyticity and the strict original U,V_3 amplitude budgets extend the "
                    + "same constructed-label factorization to a neighborhood of t. H(t)!=0 also extends "
                    + "locally, so the complete actual-source identity gives J=H f1 f2 f3 on that neighborhood. "
                    + "Additivity of analytic order, the simple branch nodes and absence of shared nodes "
                    + "therefore give analyticOrderNatAt(J,t)=1 at every actual J zero, including a boundary "
                    + "point of S. No openness of S or additional margin hypothesis is required.")),
                    Paragraph(Text(
                    "When the complex source B has a supplied smooth real restriction f, B(x)=f(x) on the real "
                    + "axis, and Qfar is mapped from a real polynomial, the iterated derivatives at zero agree "
                    + "with the real-source derivatives by uniqueness. Thus the actual H is the map of the same "
                    + "real finite extraction. The explicit quotient jets chi,U,V3 commute with conjugation at "
                    + "every complex parameter, including a zero of H under totalized division. This supplies "
                    + "all three coordinate conjugation identities used above. Under the same six uniform "
                    + "nonzero, value and derivative budgets, the same actual J therefore has real simple "
                    + "zeros and cardinality at most three on the entire closed target S; no separate "
                    + "coordinate analyticity or conjugation premise is needed. The real source realization "
                    + "and the numerical source budgets remain explicit conditions.")),
                    Paragraph(Text(
                    "For a monic complex polynomial P of degree q, supply the literal finite Appell equation "
                    + "s P''-z P'+q P=sum_{m=0}^q g_m P^(m+1), with s!=0 and g_0=g_1=0. At an actual "
                    + "root beta, retain a>0, |beta/(s a)|<=3/8, |(q-k)/(s a^2)|<=1/64 for k+2<=q, "
                    + "and sum_{m=0}^q |g_m a^(m-1)/s|<=1/16. Iterated polynomial differentiation supplies "
                    + "the literal root-jet recurrence, and exact division supplies its normalized recurrence. "
                    + "The finite maximum argument bounds every normalized jet d_k=P^(k)(beta)/a^k "
                    + "in magnitude by d_1: the higher recurrence terms cost at most (3/8+1/64+1/16) times the maximum, "
                    + "while monicity makes the top derivative nonzero. Thus, under those same conditions, "
                    + "P'(beta)!=0 and |P^(m)(beta)/P'(beta)|<=a^(m-1) for every m>=1. The literal "
                    + "finite differential operator Phi(D)P at that same root consequently satisfies "
                    + "|Phi(D)P(beta)/P'(beta)|<=sum_{m=1}^q |phi_m| a^(m-1). Its constant term vanishes "
                    + "at the root. The same-source construction below supplies the complete kernel equation, "
                    + "coarse root location and full coefficient majorant. Original-node transmission "
                    + "still requires its own signed cofactor information.")),
                    Paragraph(Text(
                    "For a complex polynomial H, an integer n different from zero and H(t) nonzero, "
                    + "the same-source value germ is explicit: psi(u)=t/(1+tu/n), "
                    + "chi(z)=z-(z^2/n) H'(z)/H(z), K(u)=(1+tu/n)^n H(psi(u))/H(t), "
                    + "and M(u)=exp(-chi(t)u) K(u). Put s=(t^2/n)chi'(t) and "
                    + "G(u)=chi(psi(u))-chi(t)+su. Differentiating these actual expressions "
                    + "gives M(0)=1, M'(0)=0, G(0)=G'(0)=0 and M'=(-su+G)M near zero.")),
                    Paragraph(Text(
                    "For every q at least one, retain the finite Taylor multiplier of M through q "
                    + "and apply it to X^q by replacing its variable with polynomial differentiation. "
                    + "The resulting value kernel P is monic of degree exactly q. The all-order "
                    + "Leibniz recurrence and the derivative-multiplication commutator give the literal "
                    + "equation sP''-XP'+qP=sum(m=0..q) g_m P^(m+1), with "
                    + "g_m=G^(m)(0)/m!. Thus the equation, monicity, exact degree and g_0=g_1=0 "
                    + "are derived from this germ; none is an independent supplied kernel premise.")),
                    Paragraph(Text(
                    "Assume s nonzero and put a=8 sqrt(q/|s|). The full coefficient budget "
                    + "sum(m=0..q) |g_m a^(m-1)/s| <= 1/16 supplies both the root-location "
                    + "and the diagonal bounds used by the scalar derivative chain. A maximum "
                    + "over the finite normalized derivative sequence first gives "
                    + "|beta| <= |s|b+q/b+sum(m=0..q)|g_m|b^m, where b=a/8. "
                    + "The same budget therefore gives |beta/(sa)| <= 5/16 and "
                    + "|(q-k)/(sa^2)| <= 1/64. At every actual root beta of P, P'(beta) "
                    + "is nonzero and |P^(m)(beta)/P'(beta)| <= a^(m-1) for every m at least one.")),
                    Paragraph(Text(
                    "A closed-disc supplier pays that full finite coefficient budget: if the actual "
                    + "G is analytic at every point of |u| <= 64a and |G(u)| <= 3|s|64a there, "
                    + "Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le and the vanishing first "
                    + "two jets give the uniform "
                    + "sum bound 1/21, smaller than 1/16, for every finite q. The finite sum uses "
                    + "geom_sum_Ico_le_of_lt_one; the source-specific disc and amplitude conditions "
                    + "are paid for the exterior source below.")),
                    Paragraph(Text(
                    "The closed-disc premises are paid for the actual extracted exterior source. "
                    + "Set E=exteriorSource of the original ZeroData after removing its exact local "
                    + "theory-D selection, and H=T_n E. One positive U is fixed before choosing "
                    + "the source, T, rho, n, t or q. For T at least 32, 0<rho<=1/8, "
                    + "n>=2^32 U log(T+2) T^2/rho^2, |t-T^2|<=T rho/32 and "
                    + "0<q<=512 log(T+2), the same H is nonzero at t, its s is nonzero and "
                    + "its actual G is analytic and satisfies the required amplitude bound on "
                    + "the closed 64a disc. Thus the auxiliary value kernel has exactly q "
                    + "distinct complex roots and the complete derivative-chain bound there. "
                    + "This statement includes complex centers t. On the real chart, with the stronger "
                    + "n threshold stated below, the separate finite recurrence and compact separated "
                    + "continuation application preserves real roots; original signed transmission "
                    + "remains an additional obligation.")),
                    Paragraph(Text(
                    "The same Cauchy and finite geometric-sum calculation works on a closed Ba disc "
                    + "for every B>1: the amplitude bound |G|<=3|s|Ba gives the complete finite "
                    + "budget at most 3/(B-1). For B=196609 this is 1/65536. One uniformly fixed "
                    + "positive U and the stronger threshold n>=2^20 (196609)^2 U log(T+2) T^2/rho^2 "
                    + "pay this larger actual-source disc, with the same complex-center and q bounds. "
                    + "Thus this smaller budget concerns the same literal H and G as the complete "
                    + "kernel equation, rather than an independently chosen analytic remainder.")),
                    Paragraph(Text(
                    "The derivative chain also gives uniform separation without choosing root labels. "
                    + "At a root beta, form Q=(Polynomial.taylor beta P).divX. Its constant coefficient "
                    + "is P'(beta), which is nonzero. Polynomial.factorial_smul_hasseDeriv gives "
                    + "Q_m=P^(m+1)(beta)/(m+1)!, so |Q_m/Q_0|<=a^m. The finite Taylor identity "
                    + "and geom_sum_Ico_le_of_lt_one show that Q has no zero in |z|<1/(2a). "
                    + "Consequently every other root gamma of the same P satisfies "
                    + "|gamma-beta|>=1/(2a). This conclusion holds for arbitrary complex coefficients.")),
                    Paragraph(Text(
                    "For fixed u away from 1+tu/n=0, H(t)=0 and H(psi(u))=0, differentiating the "
                    + "same actual germ in t gives logDeriv_t K=-(n/t^2)(chi(psi(u))-chi(t)) and "
                    + "logDeriv_t M=-(n/t^2)G(u), with t nonzero and the actual chi differentiable. "
                    + "These identities use the pinned logDeriv product, quotient and composition "
                    + "rules. The following finite normal form pays every parameter jet directly.")),
                    Paragraph(Text(
                    "For degree H at most n, finite homogenization removes the parameter singularity "
                    + "near u=0: F_t(u)=sum(j=0..n) H_j t^j (1+tu/n)^(n-j). Its coefficients have "
                    + "ordinary parameter derivatives as finite sums. For c(t)=-chi(t), every u jet "
                    + "of exp(c(t)u)F_t(u)/H(t) is a finite convolution of these coefficients, "
                    + "exponential powers and factorials. Differentiating that finite convolution, "
                    + "including the shifted exponent term and the quotient rule, supplies each "
                    + "actual M jet's parameter derivative. Pointwise differentiation and logDeriv_t M "
                    + "give the same tangent germ -(n/t^2)G(u)M(u) near zero. Eventual germ equality "
                    + "and the native all-order Leibniz rule identify the complete convolution "
                    + "derivative for every jet order, without a mixed derivative interchange premise.")),
                    Paragraph(Text(
                    "With degree H at most n and n, t and H(t) nonzero, for every finite q including "
                    + "q=0, the Taylor multiplier of GM agrees through degree q with the product of "
                    + "the Taylor multipliers of G and M. Their difference "
                    + "vanishes after substituting D on X^q, so finite operator composition gives "
                    + "partial_t P=-(n/t^2)G(D)P for this same actual H. A finite sum of HasDerivAt "
                    + "proofs supplies this identity at every evaluation point. If a complex branch "
                    + "beta has HasDerivAt at t, P_v(beta(v)) vanishes near t and P'_t(beta(t)) is "
                    + "nonzero, differentiation with the moving evaluation point gives "
                    + "beta'=(n/t^2)G(D)P(beta)/P'(beta). This conditional identity does not "
                    + "construct a root branch.")),
                    Paragraph(Text(
                    "For q at least one, s nonzero and the full scaled coefficient budget at most "
                    + "1/65536, the actual Appell equation supplies simplicity and the complete "
                    + "derivative chain. The finite operator at the root costs at most |s|/65536. "
                    + "The exact identity (n/t^2)s=chi'(t) therefore gives |beta'|<=|chi'(t)|/65536. "
                    + "For the original exterior source, one positive U fixed before Z,T,rho,n,t,q "
                    + "and beta, T>=32, 0<rho<=1/8, n>=2^20 (196609)^2 U log(T+2)T^2/rho^2, "
                    + "|t-T^2|<=T rho/32 and 0<q<=512 log(T+2) supply degree H<=n, H(t)!=0, "
                    + "n!=0, t!=0, s!=0, the entire budget and |chi'-1|<=1/128. Hence every supplied "
                    + "differentiable local root branch satisfies |beta'|<=129/8388608<1/4. "
                    + "The 1/65536 coefficient budget by itself gives the factor |chi'| in the "
                    + "velocity bound.")),
                    Paragraph(Text(
                    "Local analytic branches are also constructed for this actual kernel. The finite "
                    + "normal form makes every parameter jet analytic wherever H(t) is nonzero, and "
                    + "the finite multiplier expression makes P(t,z) jointly analytic. At a simple "
                    + "root, its right derivative is the invertible map toSpanSingleton(P'_t(beta)). "
                    + "The pinned ContDiffAt omega implicitFunction theorem therefore constructs "
                    + "a local branch with beta(t)=beta_0, AnalyticAt beta t, P_v(beta(v))=0 near t "
                    + "and uniqueness in a product neighborhood of (t,beta_0). For the original "
                    + "exterior source, choose one positive U combining the speed and root-chain "
                    + "suppliers before all source parameters. Under the same stronger n threshold, "
                    + "complex closed D/32 chart and positive q bound above, every actual root beta_0 "
                    + "has such a branch with |beta'(t)|<=129/8388608<1/4. The source supplies H(t) "
                    + "nonzero, degree H at most n and simplicity; none is a new branch premise. "
                    + "This is local existence with the derivative bound at the chosen center. A "
                    + "uniform neighborhood radius and global compatible analytic labels remain open.")),
                    Paragraph(Text(
                    "These applications use standard pinned complex analytic, implicit-function, zero-count, "
                    + "mean-value and set-cardinality results. They are bind-only with admission_basis none and "
                    + "are recorded here as source-derived applications rather than new retained D5 declarations. "
                    + "The original core signed cofactor transport and original-node response sign "
                    + "remain open. The exterior auxiliary kernel conclusions above do not "
                    + "give original-node reality, all-height exclusion, RH or strict Robin beyond 5040."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-jensen-canonical-bridge"),
                DeclarationHandle.Create(Prefix + "sourceJensenPolynomial_eq_normalizedJensen"),
                H("Source and canonical polynomial equality"),
                StatementSource.FromAuthor(Disp(Seq(
                    DegreeDomain(D(1)), Sub(F.Id("P"), Dd), Eq,
                    Call(F.Id("N"), F.Id("a"), Dd)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The independent literal source polynomial equals the canonical adapter "
                    + "at the fixed density-moment coefficient sequence. This is the preceding "
                    + "normalization theorem specialized to a and read in the reverse direction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-jensen-degree-lowering"),
                DeclarationHandle.Create(Prefix + "source_jensen_degree_lowering"),
                H("Exact source degree lowering at every complex argument"),
                StatementSource.FromAuthor(Disp(new Formula.Aligned([
                    Seq(DegreeDomain(D(2)), Domain(F.Id("v"), Complex())),
                    Seq(Call(Sub(F.Id("P"), Dd), F.Id("v")), Minus,
                        Fraction(F.Id("v"), Dd), Sp,
                        Call(Seq(Sub(F.Id("P"), Dd), Apos), F.Id("v")), Eq,
                        Call(Sub(F.Id("P"), Previous()),
                            Seq(Fraction(Previous(), Dd), Sp, F.Id("v"))))
                ]))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "P'(v) means Polynomial.derivative evaluated at v. The proof uses the "
                    + "named source-to-canonical equality at d and d-1, then evaluates the "
                    + "universal lowering identity at v. All subtraction of natural degrees "
                    + "is interpreted in Nat before coercion; d at least two supplies the "
                    + "required bounds. No root-reality, RH, positivity, analytic convergence, "
                    + "or exact polynomial-degree premise is imposed."))),
                DescribeRole.Theorem))));

    private static Formula Xx => F.Id("x");
    private static Formula Kk => F.Id("k");
    private static Formula Dd => F.Id("d");
    private static Formula Natural() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Previous() => Seq(Dd, Minus, D(1));
    private static Formula Twice(Formula f) => Seq(D(2), Sp, f);
    private static Formula Fraction(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Pow(Formula a, Formula b) => Seq(a, Caret, Grp(b));
    private static Formula Sub(Formula a, Formula b) => Seq(a, Underscore, Grp(b));
    private static Formula Call(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula N(Formula degree) => Call(F.Id("N"), F.Id("b"), degree);
    private static Formula Domain(Formula v, Formula type) =>
        Seq(Forall, Sp, v, InMacro, type, Comma, Sp);
    private static Formula DegreeDomain(Formula lower) =>
        Seq(Domain(Dd, Natural()), lower, Leq, Sp, Dd, Rightarrow, Sp);
    private static Formula GenericDomain(Formula lower) => Seq(
        Forall, Sp, F.Id("b"), Colon, Natural(), To, Real(), Comma, Sp, DegreeDomain(lower));
    private static Formula XiCenter() =>
        Call(F.Id("xiReading"), Fraction(D(1), D(2)));

    private static Formula FallingSum(Formula coefficient) => Seq(
        Sum, Underscore, Grp(Kk, Eq, D(0)), Caret, Grp(Dd), Sp,
        Fraction(Call(F.Id("descFactorial"), Dd, Kk), Pow(Dd, Kk)), Sp,
        Sub(coefficient, Kk), Sp, Pow(F.Id("X"), Kk));

    private static Formula AdapterFormula() => Disp(Seq(
        Forall, Sp, F.Id("b"), Colon, Natural(), To, Real(), Comma, Sp,
        Domain(Dd, Natural()), N(Dd), Eq,
        Call(Sub(Seq(Operatorname, Grp(F.Id("map"))), Seq(Real(), To, Complex())),
            Seq(Call(F.Id("J"), Seq(Kk, Mapsto, Sp, Kk, Bang, Sp, Sub(F.Id("b"), Kk)),
                    Dd, D(0)), Circ, Open, Fraction(D(1), Dd), Sp, F.Id("X"), Close))));

    private static Formula KernelFormula()
    {
        Formula positiveIndex = Seq(Open, F.Id("n"), Plus, D(1), Close);
        Formula abs = Seq(Bar, Xx, Bar);
        Formula first = Seq(D(4), Sp, Pow(Pi, D(2)), Sp, Pow(positiveIndex, D(4)), Sp,
            Call(Exp, Fraction(Seq(D(9), Sp, abs), D(2))));
        Formula second = Seq(D(6), Sp, Pi, Sp, Pow(positiveIndex, D(2)), Sp,
            Call(Exp, Fraction(Seq(D(5), Sp, abs), D(2))));
        Formula decay = Call(Exp, Seq(Minus, Pi, Sp, Pow(positiveIndex, D(2)), Sp,
            Call(Exp, Twice(abs))));
        return Disp(Seq(Domain(Xx, Real()), Call(F.Id("K"), Xx), Eq,
            Sum, Apos, Underscore, Grp(F.Id("n"), InMacro, Natural()), Sp,
            Open, first, Minus, second, Close, Sp, decay));
    }
}
