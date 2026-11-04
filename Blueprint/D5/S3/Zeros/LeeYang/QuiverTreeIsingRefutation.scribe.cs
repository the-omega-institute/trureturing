using System.Collections.Generic;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.LeeYang;

internal sealed class QuiverTreeIsingRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation.";
    private const string PhysicalPrefix = "D5/S3/Zeros/LeeYang/QuiverTreePhysicalE8.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/fiolmartinezmontoyariosfukelman2020quiver");
    private const string Conjecture =
        "For any tree with e edges, any fixed positive integers n₁,…,nₑ and arbitrary "
        + "ρ(kᵢ,nᵢ)>0 the polynomials P(τ,x, n₁,…,nₑ) have all their x roots on the unit circle.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive joint split weights refute the tree Lee-Yang conjecture.",
        H("A tree Ising polynomial with an off-circle root"),
        Blocks(
            Node("splits", "The positive edge splits", SplitsFormula(),
                "Section 2.2, printed p. 13 (PDF p. 14): “Assign a positive integer nᵢ to each "
                + "of the e edges of the tree graph.” “For every edge, split nᵢ into two positive "
                + "integers, nᵢ=kᵢ+(nᵢ−kᵢ) and assign each of these two integers to one of the "
                + "vertices at the ends of that edge.” Fintype.piFinset gives exactly the "
                + "configuration functions in the product of Finset.Icc 1 (n i − 1). Nat.sub "
                + "is natural-number subtraction, truncated at zero."),
            Node("mass", "Vertex masses", MassFormula(),
                "Section 2.2, printed p. 13 (PDF p. 14): “Then, if a vertex has degree dⱼ this "
                + "procedure assigns to that vertex dⱼ integers. Let mⱼ be the sum of these "
                + "integers at a given vertex; the magnetic field at that vertex is then mⱼ H.” "
                + "The source endpoint receives k i and the target endpoint receives n i − k i. "
                + "The formula displays both filtered finite sums; subtraction is Nat.sub."),
            Node("treePoly", "The weighted tree Ising polynomial", PolynomialFormula(),
                "Section 2.2, printed p. 13 (PDF p. 14), equation (2.30), defines P by summing "
                + "over all splits and all spin states, with factors ρ(kᵢ,nᵢ), τ raised to the "
                + "number of opposite-spin edges, and x raised to the sum of spin-up vertex "
                + "masses. The source says: “where ρ(kᵢ,nᵢ) is a distribution that weights "
                + "different configurations.” The coefficient type is ℝ; Polynomial.C embeds "
                + "coefficients and Polynomial.X is the indeterminate. Spins have type V → Bool, "
                + "and true means spin up. The weight rho depends jointly on the whole split."),
            Node("claim", "Conjecture 1 with its binding conventions", ClaimFormula(),
                "Section 2.2, Conjecture 1, printed p. 14 (PDF p. 15): “" + Conjecture + "” "
                + "The displayed tree condition is NamedTreePhaseTransport.NamedSpanningTree src tgt Set.univ in Lean: all edges are selected, and its nonloop, distinct and isTree fields give precisely this condition. The orientation records which endpoint receives the split parameter. The convention uses n i ≥ 2, excluding the empty split sum at n i = 1, "
                + "and τ ∈ Set.Icc (−1) 1. The source's one-edge argument uses |τ| ≤ 1. "
                + "Every allowed joint weight is strictly positive. Polynomial.map along "
                + "algebraMap ℝ ℂ is the complex coefficient polynomial; IsRoot means its "
                + "evaluation is zero. The conclusion is the complex norm ‖z‖ = 1."),
            Node("result", "Conjecture 1 is refuted for joint weights", Seq(Neg, Sp, Op("claim")),
                "The witness is the path 0 → 1 ← 2 with totals (4,4), τ = −1, and weights "
                + "W₃₁ = ((1,1,1),(1,10,1),(1,1,31)), indexed by the two splits in {1,2,3}. "
                + "Its masses are (k₁,8−k₁−k₂,k₂). The same polynomial arises from "
                + "0 → 1 → 2 with the second weight index reversed. Exact state and split "
                + "enumeration gives 48−6X+8X²−62X³+24X⁴−62X⁵+8X⁶−6X⁷+48X⁸. "
                + "It equals 2(X−1)²X³q(X+X⁻¹), where q(y)=24y³+45y²−2y−26. "
                + "The cubic discriminant is −16404; Cubic.discr_eq_prod_three_roots "
                + "would make it a square, so q cannot split over ℝ. Algebraic "
                + "closure and descent of splitting give a nonreal complex root w. A root z "
                + "of z²−wz+1=0 is nonzero and satisfies w=z+z⁻¹. It is an octic root; "
                + "if ‖z‖=1, then z⁻¹=conj z, forcing w to be real. The general product-weight "
                + "version and physical questions outside the separately described all-vertex e8 result remain open.", true,
                [DeclarationHandle.Create(PhysicalPrefix + "result")]),
            Paragraph(DefinitionDsl.Text("Analytical coefficient exposition. The following complete assignment-summed calculation is independently source-assessed analysis, not a new Lean theorem or a consequence certified by either refutation. The arbitrary-joint-weight refutation and the separate all-total-three e8 physical refutation do not certify this 123-vertex physical-weight calculation. The readable derivation is also in the existing Fiol Problems dossier. This m60 exposition is analytical and supplies no additional formal theorem.")),
            Paragraph(DefinitionDsl.Text("Fixed tree and formal coordinates. T has a unique degree-2 centre c, two degree-61 hubs h1,h2 joined to c, and 60 degree-1 leaves at each hub. Thus |E|=122, |V|=123 and there are 122 odd-degree vertices. Replace each occurrence of zeta(2n-1) in the source expansion by an independent commuting formal generator Z_(2n-1), and let F_(0,T) denote only the summand of the fixed unlabelled tree T in equation (2.19). Coefficient extraction below is in these formal generators. No algebraic independence of the numerical odd zeta values is asserted or needed.")),
            Paragraph(DefinitionDsl.Text("Coefficient and roots. For X=lambdaTilde2/lambdaTilde1, lambdaTilde1 nonzero, [Z_5^2 Z_3^120] F_(0,T) = 200*12^120*lambdaTilde1^246*(1-X)^122*Q(X). Equivalently, after homogeneous extension this is a degree-246 polynomial in the two couplings; the normalized polynomial in X is a nonzero scalar multiple of P(X)=(1-X)^122*Q(X). Q has degree exactly 124 and exactly 124 distinct simple complex roots, all on |X|=1 and none equal to 1 or -1. P has degree exactly 246. Its zeros counted with multiplicity consist of X=1 with multiplicity exactly 122 and these 124 simple other roots. There are 125 distinct roots of P. Its constant and leading coefficients are both 50300599, so it has neither a zero at X=0 nor a projective zero at infinity.")),
            Paragraph(DefinitionDsl.Text("Source boundary. For the coefficient defined directly by (2.19), all vertices are explicit in the primary formula. Identifying its rho with the Ising display (2.31) uses the stated editorial replacement of m by m+1. The calculation does not establish that replacement as an author-approved correction or an erratum. Omitting an unspecified vertex is not the model assessed here. The literal generalized Conjecture 1 fixes labelled n_i and allows arbitrary positive rho. The candidate claimPhys fixes labelled n_i and restricts rho to the all-vertex physical factor at tau=-1. The physical prose also refers to a tree contribution in the planar expansion, for which formal coefficient extraction includes all labelled assignments. These are different mathematical assertions; the new aggregate answers only the last bounded coefficient question.")),
            Paragraph(DefinitionDsl.Text("Source attribution. Fiol, Martínez-Montoya and Rios Fukelman, arXiv:2006.06379v2, PDF equations (2.15)–(2.19) and (2.30)–(2.31), supply the correlator, couplings, spin sum and external factors. Their predecessor arXiv:2003.02879v3, Section 2.3 around (44)–(46), gives complementary-split orientation invariance after split sums and m!/|Aut(T)| after total sums; individual correlator products before these sums may differ. These are source correspondences, not a priority claim. The inspected arXiv record lists v2 as latest; the inspected INSPIRE and Crossref records show no related correction. This bounded observation neither excludes all possible corrections nor establishes authorial intent.")),
            Paragraph(DefinitionDsl.Text("Exhaustive assignment partition. An assignment is a two-element subset A of the 122 named edges, with n_e=3 on A and 2 elsewhere. Thus the number of assignments is binom(122,2)=122*121/2=7381. Either both selected edges are central, one is central, or neither is central. For one central edge, the selected pendant is at its own or the opposite hub. For no central edge, the pendants are at the same or opposite hubs. This is an exhaustive disjoint classification. The degree-2 centre is unique. The hubs can be interchanged, and their leaves can be permuted independently; there are no other automorphisms. Hence |Aut(T)|=2*(60!)^2.")),
            Paragraph(DefinitionDsl.Text("Assignment orbit: Both central edges. Multiplicity 1. There are precisely two central edges. Stabilizer order 2*(60!)^2.")),
            Paragraph(DefinitionDsl.Text("Assignment orbit: One central edge and a pendant at the same hub. Multiplicity 120. 2 choices of central edge times 60 pendants at its hub. Stabilizer order 60!*59!.")),
            Paragraph(DefinitionDsl.Text("Assignment orbit: One central edge and a pendant at the opposite hub. Multiplicity 120. 2 choices of central edge times 60 opposite pendants. Stabilizer order 60!*59!.")),
            Paragraph(DefinitionDsl.Text("Assignment orbit: Two pendants at the same hub. Multiplicity 3540. 2*binom(60,2)=60*59=3540. Stabilizer order 2*60!*58!.")),
            Paragraph(DefinitionDsl.Text("Assignment orbit: Two pendants at opposite hubs. Multiplicity 3600. 60*60=3600. Stabilizer order 2*(59!)^2.")),
            Paragraph(DefinitionDsl.Text("1+120+120+3540+3600=7381. For each orbit O, its total source weight is |O|/|Aut(T)|=1/|Stab(A)|. Equal weights for the five orbit representatives would be wrong. Each ordered tuple (n1,...,n122) with two 3s occurs once in coefficient extraction. Their count is 122!/(2!*120!)=7381, which is already the number of subsets A. No additional 2!, 120!, 122! or orbit-count divisor is inserted. The source's original 1/m! has already cancelled its edge-labelling factor.")),
            Paragraph(DefinitionDsl.Text("Complete spin sum. For any up-spin set B, sum_(v in B) deg(v)=2*(number of edges within B)+|boundary B|. Thus (-1)^|boundary B| is the product of (-1)^deg(v) over v in B. Summing over every B gives exactly product_v (1+(-1)^deg(v)*X^M_v). This identity retains every spin state, and does not discard edge factors.")),
            Paragraph(DefinitionDsl.Text("Endpoints and edges. EndpointFactor(1)=2 and EndpointFactor(2)=12. A total-2 edge has only (1,1), giving binom(4,2)*2*2=24. A total-3 edge has both (1,2) and (2,1); each gives binom(6,2)*2*12=360. Therefore the two selected edges give four endpoint allocations, each adding one unit to one endpoint. This remains true for selected pendant edges.")),
            Paragraph(DefinitionDsl.Text("Vertex ratios. Writing M_v=d_v+r_v, the non-endpoint factorial factor is f_d(r)=(d+r-1)!/(r+2)!. Dividing by f_d(0)=(d-1)!/2 gives a_d(0)=1, a_d(1)=d/3 and a_d(2)=d(d+1)/12. In particular a_2(1)=2/3, a_2(2)=1/2, a_61(1)=61/3, a_61(2)=1891/6, and a_1(1)=1/3. A leaf cannot receive two increments in this model.")),
            Paragraph(DefinitionDsl.Text("Common scalar. The baseline product of vertex factorial factors is (60!)^2/2^123. Multiplying by 24^120*360^2 gives 16200*(60!)^2*12^120=18*C0, where C0=900*(60!)^2*12^120. The endpoint-factor change is already in the two 360s and must not be inserted again in a_d(r).")),
            Paragraph(DefinitionDsl.Text("Spin factor reduction. Every mass is positive. Each of the 122 odd-degree vertices supplies (1-X^M)=(1-X)*S_M. The even-degree centre supplies H_(2+r_c). Thus (1-X)^122 is common even when a selected pendant gives its leaf mass 2. Here S_m=sum_(j=0)^(m-1) X^j, U=S_61, V=S_62, W=S_63, L=1+X, and H_r=1+X^r.")),
            Paragraph(DefinitionDsl.Text("Four allocation coefficients. After division by C0 and extraction of (1-X)^122, the relevant allocation weights are: different hubs 18*(61/3)^2=7442; centre and hub 18*(2/3)*(61/3)=244; twice centre 18*(1/2)=9; twice one hub 18*(1891/6)=5673; hub and leaf 18*(61/3)*(1/3)=122; centre and leaf 18*(2/3)*(1/3)=4; two distinct leaves 18*(1/3)^2=2. The two choices of which selected edge gives the hub increment yield the doubled mixed terms in the pendant-pendant cases.")),
            Paragraph(DefinitionDsl.Text("For each A, P_A is the split- and spin-summed polynomial before the source's (-2)^m, 1/product n and 1/|Aut(T)| factors. P_A=C0*(1-X)^122*q_A. Define Q=sum_A q_A.")),
            Paragraph(DefinitionDsl.Text("Both central edges: q_A=7442*H_2*V^2 + 488*H_3*U*V + 9*H_4*U^2. Both increments at hubs; one at centre and one at a hub in two ways; both at centre. This exactly reproduces the fixed candidate's obstruction after normalization.")),
            Paragraph(DefinitionDsl.Text("Central plus same-hub pendant: q_A=5673*H_2*U*W + 122*H_2*L*U*V + 244*H_3*U*V + 4*H_3*L*U^2. Both increments at the common hub; hub and leaf; centre and hub; centre and leaf.")),
            Paragraph(DefinitionDsl.Text("Central plus opposite-hub pendant: q_A=7442*H_2*V^2 + 122*H_2*L*U*V + 244*H_3*U*V + 4*H_3*L*U^2. The two hubs; central-edge hub and opposite leaf; centre and opposite hub; centre and leaf.")),
            Paragraph(DefinitionDsl.Text("Two same-hub pendants: q_A=5673*H_2*U*W + 244*H_2*L*U*V + 2*H_2*L^2*U^2. Both increments at their common hub; one at hub and one at a leaf in two ways; both at the distinct leaves. The double-hub ratio is a_61(2), not a_61(1)^2.")),
            Paragraph(DefinitionDsl.Text("Two opposite-hub pendants: q_A=7442*H_2*V^2 + 244*H_2*L*U*V + 2*H_2*L^2*U^2. Both hubs; one hub and the other leaf in two ways; both leaves.")),
            Paragraph(DefinitionDsl.Text("Aggregate Q. H_2*(27691682*V^2 + 20763180*U*W + 1771440*L*U*V + 14280*L^2*U^2) + H_3*(59048*U*V + 960*L*U^2) + 9*H_4*U^2. The seven multipliers are H_2*V^2: 7442*(1+120+3600)=7442*3721=27691682. H_2*U*W: 5673*(120+3540)=5673*3660=20763180. H_2*L*U*V: 122*(120+120)+244*(3540+3600)=29280+1742160=1771440. H_2*L^2*U^2: 2*(3540+3600)=14280. H_3*U*V: 488+244*(120+120)=59048. H_3*L*U^2: 4*(120+120)=960. H_4*U^2: 9.")),
            Paragraph(DefinitionDsl.Text("Every monomial coefficient. Let q_k=[X^k]Q. The following formula specifies every coefficient; q_k=0 outside 0<=k<=124, and q_(124-k)=q_k. q_0=50300599, q_1=102402158, q_2=204758579; for 3<=k<=60, q_k=104231678*k - 3720026; q_61=6331788166, q_62=6354351346. For k<=60, each convolution S_a*S_b appearing here has coefficient k+1. Put K=27691682+20763180=48454862. The small multipliers are H_2; H_2*L=1+X+X^2+X^3; H_2*L^2=1+2X+2X^2+2X^3+X^4; H_3; H_3*L=1+X+X^3+X^4; H_4. For 3<=k<=60 this gives 2K*k +1771440*(4k-2)+14280*(8k-8)+59048*(2k-1)+960*(4k-4)+9*(2k-2), which is the displayed linear formula. At k=61 the finite lengths subtract 20763180+1771440+2*14280+59048+2*960+2*9=22624166 from that linear formula. At k=62 they subtract 2*27691682+2*20763180+4*1771440+8*14280+3*59048+6*960+4*9=104292664. The first three coefficients follow by direct short convolution. Reflection gives the remaining 62 coefficients.")),
            Paragraph(DefinitionDsl.Text("Exact evaluations and the full coefficient. Summing this coefficient formula gives Q(1)=400163878746. Its alternating sum gives Q(-1)=41526378. Its powers-of-i sum gives Q(i)=120034, agreeing with the direct factor evaluations below. Every coefficient of the full normalized P is determined exactly by [X^k]P=sum_(j=0)^122 (-1)^j*binom(122,j)*q_(k-j), with q outside 0..124 zero. This is the polynomial product identity, not a numerical computation.")),
            Paragraph(DefinitionDsl.Text("Degree and source normalization. S_m is real reciprocal of degree m-1, H_r of degree r, and L of degree 1. Each of the seven displayed product terms has degree exactly 124. Its constant and leading coefficients agree, all multipliers are positive, and their sum is 27691682+20763180+1771440+14280+59048+960+9=50300599. Thus Q is nonzero, has exact degree 124, and satisfies Q(X)=X^124*Q(1/X). In particular Q(1)>0, independently of the optional exact sum. Here m=122, sum_e n_e=246 and product_e n_e=9*2^120. The source factor is (-2)^122*(-1)^246/(9*2^120*|Aut(T)|)=4/(9*|Aut(T)|). Multiplying this by C0=900*(60!)^2*12^120 and using |Aut(T)|=2*(60!)^2 gives exactly 200*12^120. Every vertex coupling factor is retained, and sum_v M_v=sum_e n_e=246, giving the common homogeneous factor lambdaTilde1^246.")),
            Paragraph(DefinitionDsl.Text("Real phase-normalized function. Set F(theta)=exp(-62*i*theta)*Q(exp(i*theta)) on [0,pi]. Real coefficients and reciprocity give conjugate(F)=exp(62*i*theta)*Q(exp(-i*theta))=F. Thus F is real and continuous. The phase is never zero, so a zero of F is exactly a zero of Q at exp(i*theta).")),
            Paragraph(DefinitionDsl.Text("61st-root grid, including its phase. For a_j=2*pi*j/61, 1<=j<=30, put X=exp(i*a_j). Then X^61=1 and X is not 1. Hence U=0, V=1, and all terms except 27691682*H_2*V^2 vanish. Also X^(-62)=X^(-1). Therefore F(a_j)=27691682*(X+X^(-1))=55383364*cos(a_j). It is strictly positive for j=1,...,15 and strictly negative for j=16,...,30; no point equals pi/2.")),
            Paragraph(DefinitionDsl.Text("62nd-root grid, including all surviving terms. For b_j=pi*j/31, 1<=j<=31, X=exp(i*b_j) obeys X^62=1 and X is not 1. Thus V=0, U=-X^(-1), W=1 and X^(-62)=1. Set t=X+X^(-1)=2*cos(b_j). The surviving four contributions are -20763180*t; 14280*t*(t+2); 960*(t^2+t-2); and 9*(t^2-2). Their sum is F(b_j)=15249*t^2-20733660*t-1938. No H_3*L*U^2 or H_4 term was dropped.")),
            Paragraph(DefinitionDsl.Text("Exact signs on every 62nd-root sample. For 1<=j<=15, 0<t<=2, so 15249*t^2-20733660*t-1938 <= (30498-20733660)*t-1938 < 0. For 16<=j<=31, monotonicity of cosine gives t<=-2*sin(pi/62). Concavity of sine gives sin(u)>=2u/pi on [0,pi/2], so t<=-2/31. The quadratic term is nonnegative, and consequently F(b_j)>=41467320/31-1938=41407242/31>0. At b_31=pi this gives the exact value F(pi)=Q(-1)=41526378.")),
            Paragraph(DefinitionDsl.Text("The additional midpoint and the theta=0 endpoint. At X=i, U=1, V=L=1+i, H_2=0, H_3=1-i and H_4=2. Hence Q(i)=2*(59048+960)+18=120034. Because i^(-62)=-1, F(pi/2)=-120034<0. At theta=0 the quotient Q, rather than a rational expression with denominator 1-X, is used: F(0)=Q(1)=400163878746>0. There is no singularity at this endpoint.")),
            Paragraph(DefinitionDsl.Text("Ordering, count, and alternation. For 1<=j<=30, b_j<a_j<b_(j+1): the second inequality is equivalent to 62*j<61*(j+1), which holds since j<61. Also a_15=30*pi/61<pi/2 and b_16=16*pi/31>pi/2. Thus the strictly ordered list is 0,b_1,a_1,...,b_15,a_15,pi/2,b_16,a_16,...,b_30,a_30,b_31=pi. It has 1+31+30+1=63 points. Signs are +,-,+,...,-,+,-,+,-,...,+,-,+. They alternate strictly, including across both sides of pi/2. The extra midpoint is essential: the two grids alone do not give 62 sign changes.")),
            Paragraph(DefinitionDsl.Text("Exhaustive root count and simplicity. The intermediate value theorem gives a zero of F in each of the 62 disjoint open intervals between successive sample points. Exponentiation is injective on (0,pi), so these give 62 distinct roots of Q in the open upper semicircle. Real coefficients give 62 conjugate roots in the open lower semicircle, disjoint from the first set. A nonzero degree-124 polynomial cannot have more than 124 distinct complex roots. These roots therefore exhaust its degree; every root is simple and there is no room for any off-circle, real-axis, repeated, or additional root. The nonzero endpoint evaluations separately confirm Q(1) and Q(-1) are not zero.")),
            Paragraph(DefinitionDsl.Text("Multiplicity in the full coefficient. Multiplication by (1-X)^122 adds exactly the root 1 of multiplicity 122 because Q(1)>0. The scalar 200*12^120 is nonzero, so it changes no root or multiplicity. The degree is 122+124=246 and all zeros counted with multiplicity lie on the unit circle.")),
            Paragraph(DefinitionDsl.Text("Fixed-labelled target preserved. The both-central placement has exactly q_CC=7442*H_2*V^2+488*H_3*U*V+9*H_4*U^2, matching the supplied fixed-model source. Its fixed-assignment off-circle argument and the new unit-circle aggregate concern different polynomials. The aggregate result does not retract the fixed-labelled mathematical target or provide a new current kernel verdict for the existing candidate. In particular, one cannot present that placement alone as the full assignment-summed coefficient, and one cannot use the positive aggregate to establish the universal fixed-labelled claimPhys. The retained candidate targets result : Not claimPhys for every finite tree with at least two edges, every fixed assignment n_e>=2, all physical factors and tau=-1. This m60 candidate has no current kernel or admission verdict here. The separate all-total-three e8 result refutes the registered all-vertex fixed-labelled claim; it does not identify that claim with the assignment-summed planar contribution. In particular, the disagreement over identifying a fixed-labelled external problem with the assignment-summed planar contribution is not resolved by this example. The separate two-edge boundary argument remains a prose result. An unguarded generic strict degree-zero bound fails; its unused proposed n>=1, degree-2n correction is not an accepted theorem.")),
            Paragraph(DefinitionDsl.Text("Remaining domain. This statement concerns tau=-1, this tree, this formal monomial, and the all-vertex source construction. It does not concern an individual fixed-labelled assignment, other multisets, other trees, other tau, the sum across all trees, or a full infinite coupling series. No further coefficient or root-location step is missing for this precisely bounded all-vertex formal coefficient. Authorial intent and the general assignment-summed physical tree conjecture remain unresolved by this calculation. Conjecture 2, which sums over trees, and the conditional Wilson-loop assertions also remain unresolved here. No general-conjecture settlement or literature-priority claim is made.")))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        bool theorem = false, IEnumerable<DeclarationHandle>? resolutionMembers = null) => Describe.Lean(
            DescribeId.Create("quiver-tree-ising-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            theorem ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(DefinitionDsl.Text(prose))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition,
            theorem ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("fiol-martinezmontoya-riosfukelman-2020-tree-lee-yang"),
                ResolutionKind.Refuted,
                resolutionMembers ?? Array.Empty<DeclarationHandle>()) : null);

    private static Formula Id(string value) => F.Id(value);
    private static Formula Op(string name) => Seq(Operatorname, Grp(Id(name)));
    private static Formula Q(string owner, string member) => Seq(Op(owner), Dot, Op(member));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula App(Formula function, params Formula[] args)
    {
        var items = new List<Formula>();
        foreach (var arg in args) { if (items.Count > 0) items.Add(Comma); items.Add(arg); }
        return Seq(function, Parenthesized(Seq([.. items])));
    }
    private static Formula Var(string name, Formula type) => Parenthesized(Seq(Id(name), Colon, type));
    private static Formula Inst(string name, string type) =>
        Seq(OpenBracket, Call(name, Id(type)), CloseBracket);
    private static Formula Nat => Op("Nat");
    private static Formula Real => Op("Real");
    private static Formula Complex => Op("Complex");
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Var(name, type), Comma, body);
    private static Formula Fun(string name, Formula type, Formula body) =>
        Seq(Op("fun"), Sp, Var(name, type), Mapsto, Sp, body);
    private static Formula Binders(bool vertices = true) => vertices
        ? Seq(Forall, Sp, Var("V", Op("Type")), Var("E", Op("Type")),
            Inst("Fintype", "V"), Inst("DecidableEq", "V"),
            Inst("Fintype", "E"), Inst("DecidableEq", "E"),
            Var("src", Arrow(Id("E"), Id("V"))), Var("tgt", Arrow(Id("E"), Id("V"))))
        : Seq(Forall, Sp, Var("E", Op("Type")), Inst("Fintype", "E"), Inst("DecidableEq", "E"));
    private static Formula Edge(string map) => Call(map, Id("i"));
    private static Formula Pair() => Call("s", Edge("src"), Edge("tgt"));
    private static Formula NatSub(Formula a, Formula b) => App(Q("Nat", "sub"), a, b);
    private static Formula Unfiltered(string type) =>
        Parenthesized(Seq(Q("Finset", "univ"), Colon, Call("Finset", Id(type))));
    private static Formula Filter(string type, string name, Formula condition) =>
        App(Seq(Unfiltered(type), Dot, Op("filter")), Fun(name, Id(type), condition));
    private static Formula SumOver(string name, Formula set, Formula body) =>
        Seq(new Formula.Subscript(Sum, Mem(Id(name), set)), body);
    private static Formula SplitsFormula() => Seq(Binders(false), Var("n", Arrow(Id("E"), Nat)), Comma,
        Eqn(Call("splits", Id("n")), App(Q("Fintype", "piFinset"), Fun("i", Id("E"),
            App(Q("Finset", "Icc"), D(1), NatSub(Call("n", Id("i")), D(1)))))));
    private static Formula MassFormula() => Seq(Binders(),
        Var("n", Arrow(Id("E"), Nat)), Var("k", Arrow(Id("E"), Nat)), Var("v", Id("V")), Comma,
        Eqn(Call("mass", Id("src"), Id("tgt"), Id("n"), Id("k"), Id("v")),
            Seq(Parenthesized(SumOver("i", Filter("E", "i", Eqn(Edge("src"), Id("v"))), Call("k", Id("i")))),
                Plus, Parenthesized(SumOver("i", Filter("E", "i", Eqn(Edge("tgt"), Id("v"))),
                    NatSub(Call("n", Id("i")), Call("k", Id("i"))))))));
    private static Formula PolynomialFormula()
    {
        var states = Arrow(Id("V"), Op("Bool"));
        var opposite = Filter("E", "i", new Formula.Relation(
            App(Id("st"), Edge("src")), FormulaRelationOperator.NotEqual, App(Id("st"), Edge("tgt"))));
        var count = Seq(Parenthesized(opposite), Dot, Op("card"));
        var exponent = SumOver("v", Filter("V", "v", Eqn(Call("st", Id("v")), Op("true"))),
            Call("mass", Id("src"), Id("tgt"), Id("n"), Id("k"), Id("v")));
        var stateSum = Seq(new Formula.Subscript(Sum, Seq(Id("st"), Colon, states)),
            App(Q("Polynomial", "C"), new Formula.Power(Id("tau"), count)), Cdot, Sp,
            new Formula.Power(Q("Polynomial", "X"), exponent));
        return Seq(Binders(), Var("n", Arrow(Id("E"), Nat)),
            Var("rho", Arrow(Parenthesized(Arrow(Id("E"), Nat)), Real)), Var("tau", Real), Comma,
            Eqn(Call("treePoly", Id("src"), Id("tgt"), Id("n"), Id("rho"), Id("tau")),
                SumOver("k", Call("splits", Id("n")), Seq(App(Q("Polynomial", "C"), Call("rho", Id("k"))),
                    Cdot, Sp, Parenthesized(stateSum)))));
    }
    private static Formula ClaimFormula()
    {
        var positiveTotals = All("i", Id("E"),
            new Formula.Relation(D(2), FormulaRelationOperator.LessThanOrEqual, Call("n", Id("i"))));
        var positiveWeights = All("k", Arrow(Id("E"), Nat), Imp(Mem(Id("k"), Call("splits", Id("n"))),
            new Formula.Relation(D(0), FormulaRelationOperator.LessThan, Call("rho", Id("k")))));
        var poly = Call("treePoly", Id("src"), Id("tgt"), Id("n"), Id("rho"), Id("tau"));
        var mapped = App(Seq(Parenthesized(poly), Dot, Op("map")), Call("algebraMap", Real, Complex));
        var root = App(Seq(Parenthesized(mapped), Dot, Op("IsRoot")), Id("z"));
        var norm = new Formula.Norm(Id("z"));
        var zeros = All("tau", Real, Imp(Mem(Id("tau"), App(Q("Set", "Icc"),
            Parenthesized(Seq(Minus, D(1), Colon, Real)), D(1))),
            All("z", Complex, Imp(root, Eqn(norm, D(1))))));
        var body = Seq(Binders(), Comma, Imp(Parenthesized(And(Parenthesized(All("i", Id("E"), new Formula.Relation(
                    Edge("src"), FormulaRelationOperator.NotEqual, Edge("tgt")))),
                And(App(Q("Function", "Injective"), Fun("i", Id("E"), Pair())),
                    Seq(Parenthesized(App(Q("SimpleGraph", "fromEdgeSet"),
                        App(Q("Set", "range"), Fun("i", Id("E"), Pair())))), Dot, Op("IsTree"))))),
            All("n", Arrow(Id("E"), Nat), Imp(Parenthesized(positiveTotals),
                All("rho", Arrow(Parenthesized(Arrow(Id("E"), Nat)), Real),
                    Imp(Parenthesized(positiveWeights), zeros))))));
        return Eqn(Op("claim"), Parenthesized(body));
    }
}
