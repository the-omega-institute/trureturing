using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Separation;

internal sealed class FixedSkeletonWeightedInclusionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common suffix replays residual evaluations across nonnested cuts of the same composed task.",
        H("Common Suffix Replay Across Pair Cuts"),
        Blocks(
            Paragraph(Text(
                "Let I index pairs with distinct first and second coordinate labels. For each i, "
                + "take nonempty alphabets X_i and Y_i, an output type Z_i, and a total map "
                + "f_i:X_i times Y_i -> Z_i. Inputs range over the full independent product. "
                + "An arbitrary total G on the product of Z_i defines the same task at both cuts. "
                + "The index set and output types need not be finite for this replay equality.")),
            Paragraph(Text(
                "A cut B is described by first-endpoint indices B_1 and second-endpoint indices B_2; "
                + "a cut P has indices P_1 and P_2. Assume B_2 is contained in B_1, P_2 is contained "
                + "in P_1, and P_2 is contained in B_2. A chosen subset A of I marks designated pairs. "
                + "For ordinary indices outside A, every first endpoint read by B is also read by P. "
                + "Each ordinary map has one surjective row and one surjective column, separately; "
                + "no condition is imposed on its other slices. These conditions permit nonnested cuts.")),
            Paragraph(Text(
                "Put E=A intersect (P_1 minus B_1). Every pair in E is untouched by B and opened "
                + "only at its first endpoint by P. Group B prefixes only by designated endpoint "
                + "values read in B and absent from P: first labels in A intersect (B_1 minus P_1), "
                + "and second labels in A intersect (B_2 minus P_2). Write C_c for the group with "
                + "these values equal to c. Values in B intersect P remain free within the group.")),
            Paragraph(Text(
                "For x in the product of X_i over E, let S_x be the product of the row images "
                + "f_i(x_i,Y_i). For z in S_x and an assignment d to all endpoints outside B and "
                + "outside pairs E, H_z^b(d) applies G to z on E and to the actual pair outputs "
                + "obtained by joining b and d elsewhere. Every H coordinate has exactly this "
                + "same labelled residual domain. A P response uses the complete independent "
                + "product of endpoints outside P as its suffix domain.")),
            Describe.Lean(
                DescribeId.Create("nonnested-common-suffix-replay"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion.nonnested_common_suffix_replay"),
                H("One suffix for every prefix in a designated group"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There is a map q taking x and any B prefix b to an actual P prefix. "
                        + "For every c,x,z,d with z in S_x, one P suffix s works for every b in C_c: "
                        + "the P response at q(x,b), evaluated at s, equals H_z^b(d). The choice of "
                        + "s may depend on c,x,z,d, but is independent of the varying prefix b.")),
                    Paragraph(Text(
                        "Choose a surjective ordinary row, a surjective ordinary column, and sections "
                        + "of these slices. On designated endpoints, q copies B values shared with P "
                        + "and inserts x at E. A designated B value absent from P is supplied by c "
                        + "in the suffix; a designated value absent from B is supplied by d. For each "
                        + "pair in E, choose its second endpoint to realize z in the selected row.")),
                    Paragraph(Text(
                        "An ordinary pair completed in B and P copies both endpoints. If completed "
                        + "in B but its second endpoint lies outside P, q encodes its actual output "
                        + "using the column section and the suffix uses the fixed column endpoint. "
                        + "For a half-read ordinary B pair, q copies its first endpoint and the suffix "
                        + "copies its second endpoint from d. For an ordinary pair untouched by B but "
                        + "opened by P, q uses the fixed row endpoint and the suffix uses the row "
                        + "section to preserve its output in d. If untouched by both cuts, both "
                        + "endpoints come from d. Comparing every pair output proves the equality "
                        + "before applying the same G. Empty E, empty groups of designated labels, "
                        + "singleton alphabets and constant G are included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("row-image-real-extrema"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion.row_image_real_extrema"),
                H("Separate attained real cover and packing optima"),
                StatementSource.FromAuthor(RealExtremaStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X and Z be finite types, let Y be a type, and let phi:X times Y -> Z "
                        + "have every effective output attained by some actual endpoint pair. "
                        + "A(z,x) is 1 exactly when some y has phi(x,y)=z, and is 0 otherwise. "
                        + "No surjectivity of every individual row or column is required.")),
                    Paragraph(Text(
                        "P(mu) means that mu:X -> R is nonnegative and, for every z, the sum of "
                        + "mu(x) over actual incident rows is at least 1. Q(v) means that v:Z -> R "
                        + "is nonnegative and, for every x, the sum of v(z) over its actual row "
                        + "image is at most 1. R denotes the real numbers. B_X and B_Z mean that "
                        + "all coordinates lie in [0,1]. S_X and S_Z denote the corresponding finite "
                        + "coordinate sums. L(a,b) means the real comparison a <= b.")),
                    Paragraph(Text(
                        "There are real lambda and w in their respective boxes satisfying P(lambda) "
                        + "and Q(w). The cover sum of lambda is no larger than that of every real "
                        + "feasible mu, and the packing sum of w is no smaller than that of every "
                        + "real feasible v. Competitors are neither assumed rational nor bounded by 1. "
                        + "This result establishes the two optima separately. Their equal real values "
                        + "are established below. Rational optimizing certificates and the same-law weighted entropy bound "
                        + "remain additional obligations for the full weighted inclusion theorem.")),
                    Paragraph(Text(
                        "Clipping an arbitrary feasible cover at 1 preserves every actual coverage "
                        + "constraint: an incident weight already at least 1 supplies the constraint "
                        + "alone, and otherwise each incident weight is unchanged. The clipping "
                        + "decreases the sum. Minimize the continuous sum on the resulting nonempty "
                        + "closed feasible cube. For the dual, an actual row containing z bounds its "
                        + "nonnegative weight by 1. Maximize the sum on the nonempty closed feasible "
                        + "set in that cube. Zero weights, repeated rows, singleton effective images "
                        + "and singleton empty products are included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("row-image-real-duality"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion.row_image_real_duality"),
                H("Equal attained real cover and packing values"),
                StatementSource.FromAuthor(RealDualityStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Use the same finite X, actual phi and effective Z, with Z nonempty. "
                        + "P,Q,S_X,S_Z and L have exactly the meanings above. There exist real "
                        + "lambda and w satisfying the actual primal and dual constraints, with "
                        + "equal sums. Lambda minimizes over every real feasible cover, and w "
                        + "maximizes over every real feasible packing. Neither an optimizer nor "
                        + "its objective value is an input assumption.")),
                    Paragraph(Text(
                        "For an attained primal optimum tau>0, put gamma=1/tau. The convex image "
                        + "of the real standard simplex under the actual incidence map is disjoint "
                        + "from the open convex set of vectors whose every coordinate exceeds gamma: "
                        + "a vector in their intersection could be rescaled by its smallest actual "
                        + "coverage to contradict primal optimality. Open geometric separation gives "
                        + "a real functional. Unbounded positive coordinate directions force its "
                        + "coefficients to be nonpositive. Their negations have positive total mass; "
                        + "normalize that mass and gamma to obtain an actual feasible dual with sum "
                        + "tau. Direct weak duality proves optimality against all real competitors.")),
                    Paragraph(Text(
                        "The witnesses in this theorem are real. Rational optimizer reconstruction "
                        + "from original active rational constraints and the weighted entropy proof "
                        + "from one actual relation law remain unproved here. This statement alone "
                        + "does not settle the original weighted inclusion, its minimum of two bounds, "
                        + "its global layer accounting or its Boolean sharpness clauses."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("active-constraint-kernel-zero"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion.active_constraint_kernel_zero"),
                H("Original active normals determine an extreme point"),
                StatementSource.FromAuthor(ActiveStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For finite coordinate and constraint types I,J, let a_j be real linear functionals, b_j real constants, and K={u: forall j, a_j(u)<=b_j}. Let v be an extreme point of K. Active(v,j) means a_j(v)=b_j. A real direction d vanishes whenever every original active normal evaluates to zero on d. The identifier zero denotes the zero scalar or vector. Inactive slacks provide one positive finite perturbation radius. Both v plus and minus epsilon d remain feasible, and their midpoint is v; extremality forces d=0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rational-extreme-point"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion.rational_extreme_point"),
                H("Rational coordinates from original active rows"),
                StatementSource.FromAuthor(RationalExtremeStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For finite coordinate and original constraint types I,J, take A:J times I -> Q "
                    + "and b:J -> Q. Matrix(J,I,Q) denotes these rational matrices. Let K(A,b) consist of real vectors u satisfying sum_i cast(A(j,i))*u(i)<=cast(b(j)) "
                    + "for every j. Every extreme point v of this original real polyhedron is the coordinatewise "
                    + "real cast C_I(q) of some q:I -> Q. Neither nonempty types nor a rational optimum value are assumed. "
                    + "Restrict A to precisely its original active rows at v. The retained active-normal theorem makes "
                    + "their real kernel zero. Cast rational kernel vectors to obtain the rational kernel result. "
                    + "The rational Gram matrix therefore admits a rational solution for the original active right sides. "
                    + "Casting this equation and real Gram uniqueness identify that solution with v. "
                    + "No objective-value row is part of the reconstruction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("row-image-rational-duality"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion.row_image_rational_duality"),
                H("Equal rational certificates optimal among all real feasible vectors"),
                StatementSource.FromAuthor(RationalDualityStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let X and Z be finite, with Z nonempty, let Y be any type, and let phi:X times Y -> Z "
                    + "attain each z at some actual pair. A(z,x)=1 exactly when some y satisfies phi(x,y)=z. "
                    + "P_Q(lambda) and Q_Q(w) are nonnegative rational actual covering and packing constraints. "
                    + "Their coordinate sums S_X(lambda) and S_Z(w) are equal in Q. C_X and C_Z are coordinatewise "
                    + "casts into the reals. P and Q without subscripts are the real feasibility predicates above. "
                    + "There exist rational lambda and w satisfying these constraints, whose real casts minimize "
                    + "and maximize against every real feasible mu and v, respectively. Rationality and attainment "
                    + "are conclusions, not input premises; no uniform slice-surjectivity is required.")),
                    Paragraph(Text(
                        "Use the retained real extrema and open-separation duality. Each attained optimum face is "
                        + "closed and nonempty. The primal face lies in the nonnegative box bounded by its fixed sum; "
                        + "the dual face lies in the unit box because every effective output belongs to an actual row. "
                        + "Select extreme points of these compact exposed faces and transport extremality to the original "
                        + "feasible polyhedra. Reconstruct rational coordinates from original nonnegativity and incidence "
                        + "rows only, then transfer feasibility, equality and the unrestricted real optimal comparisons. "
                        + "Zero dual weights, singleton effective images, repeated rows and singleton empty products are included. "
                        + "This certificate result does not prove same-law weighted entropy, global layer bounds, the literal "
                        + "minimum, the least uniform exponent or Boolean sharpness of original theorem33."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fractional-submodular-cover"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion.fractional_submodular_cover"),
                H("A finite fractional cover for a submodular function"),
                StatementSource.FromAuthor(FractionalCoverStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let A be a type with decidable equality, R a finite row type, U a finite subset of A, "
                    + "and S_r subsets of U. H maps finite subsets of A to real numbers, H(empty)=0, "
                    + "H is monotone under inclusion, and H(s union t)+H(s intersection t)<=H(s)+H(t). "
                    + "The real weights w_r are nonnegative, and every a in U has sum of incident w_r at least 1. "
                    + "SubmodularCoverAssumptions denotes exactly these premises, and L(a,b) denotes a<=b. "
                    + "Then H(U)<=sum_r w_r H(S_r). Empty U, empty selected sets, repeated row labels and zero "
                    + "weights are allowed. The proof inducts on U using the contracted function "
                    + "H(insert a,t)-H({a}) and the actual weighted incidence of a."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-coordinate-entropy"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion.weighted_coordinate_entropy"),
                H("Fractional coordinate entropy on one actual law"),
                StatementSource.FromAuthor(WeightedEntropyStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "X,A,R are arbitrary finite sample, attribute and row types. V_a are finite, possibly "
                    + "different value types. p:X->real is nonnegative and sums to 1. Each u_a:X->V_a is an "
                    + "actual readout. For S subset A, tuple_S(x)=(u_a(x)) for a in S, and "
                    + "H_p(S) is Shannon entropy in nats of pushforward tuple_S p. Every law is a literal "
                    + "pushforward of this same p. L means <=. LawAndCover denotes p>=0, sum p=1 and the following cover premises. The real row weights w_r are nonnegative and their "
                    + "sum over rows containing each attribute is at least 1. No independence or positive "
                    + "marginal premise is used. Empty selected subsets have singleton tuple carrier and entropy 0; "
                    + "repeated rows and zero weights remain included. This statement alone does not prove "
                    + "the original fixed-skeleton global bounds, literal minimum or Boolean sharpness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fractional-relation-log-bound"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion.fractional_relation_log_bound"),
                H("Fractional entropy on actual relation images"),
                StatementSource.FromAuthor(RelationLogStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "C,A,R are finite types, C is nonempty, and the finite V_a may differ by attribute. "
                    + "H:C->product_a V_a is an actual tuple family. S_r subset A and w_r>=0 cover every "
                    + "attribute with incident total at least 1. Cover denotes exactly nonnegativity and these coverage constraints; L means <=. N(H)=card(range H). P_r(H) is the "
                    + "actual range of the S_r coordinate restriction of H, not its ambient tuple carrier. "
                    + "The inequality uses the uniform law on range H and literal pushforwards of that one "
                    + "law. Its restriction-image lifts are normalized and their injective inclusions preserve "
                    + "entropy. Empty selected sets, repeated rows, zero weights and singleton relations are included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("grouped-response-bound"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion.grouped_response_bound"),
                H("A grouped bound for the same actual task"),
                StatementSource.FromAuthor(GroupedBoundStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "I and O and all endpoint/effective alphabets X_i,Y_i,Z_i are finite; X_i,Y_i are nonempty. "
                    + "The maps phi_i and total G define one actual F on the complete labelled endpoint product. "
                    + "Use designated and B_1,B_2,P_1,P_2 with B_2 subset B_1, P_2 subset P_1, P_2 subset B_2, "
                    + "and every ordinary first endpoint touched by B also in P. Every ordinary map has some "
                    + "surjective row and some surjective column; other slices can be constant. Each designated "
                    + "effective output is attained at an actual pair. E=designated intersect (P_1 minus B_1). "
                    + "For each assignment c to only the designated endpoints in B minus P, C_c is the actual "
                    + "group of B prefixes. Shared B intersect P designated values remain variable. For any "
                    + "nonnegative real w_x on product_i_in_E X_i covering every z in product_i_in_E Z_i by "
                    + "actual product row incidence, K_c is the cardinality of the actual B response image on C_c, "
                    + "ReplayAndCover denotes exactly the cut, ordinary-slice, designated-attainment and covering premises just stated; L means <=, "
                    + "and kappaP the cardinality of the full actual P response image. Then K_c<=kappaP^(sum_x w_x). "
                    + "One b-independent surjective full-suffix map identifies group responses with actual residual "
                    + "tuples. The original common replay bounds every actual row image by kappaP. E empty gives "
                    + "one residual-function attribute, not zero attributes. This is a per-group, per-cut bound; "
                    + "optimal product-value identification, group-union counting, every original skeleton layer, "
                    + "the separate coefficient-one bound and Boolean sharpness remain additional obligations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("grouped-optimal-product-bound"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion.grouped_optimal_product_bound"),
                H("The actual product optimum in the grouped bound"),
                StatementSource.FromAuthor(GroupedOptimalStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Use exactly the finite actual task, cuts, designated-only group C_c, weak ordinary "
                    + "some-row/some-column surjectivity and designated effective-output attainment of the "
                    + "preceding grouped theorem. ReplayPremises denotes those premises. rowCoverNumber(phi_i) "
                    + "is the real sum of the rational optimal primal supplied by row_image_rational_duality, "
                    + "whose real cast minimizes against every real feasible competitor. It is not an assumed "
                    + "rational optimum. Write tau_i for this number, E=designated intersect(P_1 minus B_1), "
                    + "and K_c,kappaP for the same actual response-image cardinalities. Tensor factor primal "
                    + "and dual weights are feasible for the actual product incidence, including zero weights "
                    + "and empty products. Their two objectives equal product_i_in_E tau_i. Compare the "
                    + "actual product optimizer with these tensors in both primal and dual directions to "
                    + "identify its attained real optimum with that product. The grouped bound uses that "
                    + "actual product primal, so K_c<=kappaP^(product_i_in_E tau_i). L means <=. "
                    + "The statement does not yet sum groups or derive the original permutation's all-layer "
                    + "bounds, literal minimum or one-addition-block sharpness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonnested-cut-product-bound"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion.nonnested_cut_product_bound"),
                H("A whole-cut bound with the designated group coefficient"),
                StatementSource.FromAuthor(WholeCutStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Use exactly the actual task and ReplayPremises of the preceding theorem. For these "
                    + "arbitrary compatible nonnested cuts, E=designated intersect(P_1 minus B_1). Q is the "
                    + "complete independent product of designated endpoint values in B minus P, separately "
                    + "for first and second labels; d(B,P)=card Q. kappaB and kappaP count the full actual "
                    + "B and P response images for this same phi and G. Each B prefix lies in the group "
                    + "labelled by its actual Q values. Choosing one representative of each full B response "
                    + "injects that image into the disjoint sum of its grouped response images. Groups may "
                    + "have overlapping response values; this only decreases the full count. Therefore "
                    + "kappaB<=d(B,P)*kappaP^(product_i_in_E tau_i), with tau_i the attained real row-cover "
                    + "values defined above. L means <=. Empty E and Q, initial and terminal compatible "
                    + "cuts, singleton effective images and constant G are included. This per-cut theorem "
                    + "does not itself derive compatible cuts from every original labelled permutation or "
                    + "prove the literal minimum and Boolean sharpness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-labelled-upper-minimum"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion.original_labelled_upper_contract"),
                H("Every original labelled normalized layer and both upper bounds"),
                StatementSource.FromAuthor(OriginalUpperStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "I is a finite pair index type and each endpoint is the distinct label (i,false) or (i,true). "
                    + "An oriented position bijection s maps these labels onto Fin(2 card I). Completion ranks "
                    + "count strictly earlier second positions; their constructed bijection gives cn(s) with "
                    + "first and second positions 2 rank(i) and 2 rank(i)+1. The full independent labelled "
                    + "product carries the same phi and total G at every cut. All finite X_i,Y_i are nonempty, "
                    + "every effective Z_i is attained, and ordinary maps need only some surjective row and "
                    + "some surjective column. There is at least one ordinary pair. L denotes <=. "
                    + "tau_i is the attained real optimal row cover; T is its product over designated pairs, "
                    + "D=product_designated(card X_i card Y_i), and Theta is the finite maximum over ordinary "
                    + "k of product_i_in_N_k tau_i, where N_k consists of designated strict enclosing pairs. "
                    + "W is the maximum actual response-image cardinal over all cuts 0 through 2 card I. "
                    + "The conclusion is Wcn<=min(Wpi^T,D Wpi^Theta). It also gives exact initial capacity one, "
                    + "terminal capacity card(range F), capacity one for every constant task, both directions "
                    + "of the normalized cut-family equivalence, and same-labelled-suffix response-cardinality "
                    + "transport. The last clause is written as BoundaryTransport in the formula. "
                    + "Matched before/after-completion cuts have Q singleton and yield coefficient one. "
                    + "The latest touched ordinary first label is chosen from the actual finite touched set, "
                    + "giving E subset N_k; missing designated raw coordinates are filled to prove card Q<=D. "
                    + "If no ordinary pair is touched the constructed comparison cut is initial. Empty E, "
                    + "half pairs, singleton images and constant G remain in the statement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-optimal-row-certificate"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion.integer_optimal_certificate"),
                H("Exact integer scaling of the attained rational dual"),
                StatementSource.FromAuthor(IntegerCertificateStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For finite nonempty A,B and finite Z, phi:A times B -> Z is onto its effective alphabet. "
                    + "The preserved real/rational primal-dual theorem supplies the actual nonnegative optimal "
                    + "rational w. Its finite matrix denominator gives an integer L>0 and natural ell_z, "
                    + "with sum_z ell_z=L tau and every actual row sum at most L. R_x is the actual image "
                    + "phi(x,B). Zero weights are included. No rationality, optimum value or denominator is "
                    + "assumed. This consumed supplier application supplies no new-content or escape credit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("scalar-boolean-raw-layer-signatures"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion.raw_layer_signature_bounds"),
                H("Actual Boolean signatures at every original layer"),
                StatementSource.FromAuthor(RawSignaturesStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "R and S index the original designated and ordinary pairs. Fix an ordinary k, N_k its "
                    + "strict designated containment neighborhood, and the actual product selector phi_N on "
                    + "XP=product_N X_i, YP=product_N Y_i, ZP=product_N Z_i. Let m>=2, L be natural and "
                    + "ell:ZP->Nat have sum_z_in_phi_N(x,YP) ell_z<=L for every actual x. K is the heterogeneous "
                    + "table product_z ZMod(m^ell_z). Only k's two endpoint alphabets and effective output are K; "
                    + "its map is addition transported through the original conditional alphabet equivalences. "
                    + "Every other ordinary alphabet is Bool with fixed ignored XOR. The total scalar task is "
                    + "decide((a+b)_(phi_N(x,y))=0). kappa(t) uses the actual full labelled suffix at raw cut t. "
                    + "For all natural t: before a_k, kappa<=card XP; between a_k and b_k, "
                    + "kappa<=card XP*m^L; after b_k, kappa<=card XP*card YP*m^L. The middle signature "
                    + "retains x and a restricted to that actual row. The final signature retains x, the "
                    + "observed designated Y extension and positive-weight zero flags. Zero-weight cells "
                    + "have modulus one and forced true flags. Ignored reads do not enlarge these signatures. "
                    + "The row condition here is discharged internally by the attained certificate in the final theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("scalar-boolean-normalized-table-injection"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion.normalized_table_injection"),
                H("One common normalized suffix distinguishes all tables"),
                StatementSource.FromAuthor(NormalizedInjectionStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Use the same original R+S skeleton, fixed designated effective onto maps and constructed "
                    + "one-addition-block Boolean family. At the actual normalized half cut immediately after "
                    + "k's first label, lowerPrefix(a) varies exactly that table input and fixes every other "
                    + "read endpoint. All selectors in N_k remain unread. Given two distinct tables, choose "
                    + "a differing selector coordinate z; onto product designated maps realize z in a common "
                    + "suffix, whose second table is -a. The actual scalar response for a is true and the "
                    + "other response is false. The ResponseMap(lowerPrefix) notation denotes a -> the actual normalized response at lowerPrefix(a). L denotes <= and LT denotes <. This map is injective on K, hence m^(sum ell_z)<=Wcn "
                    + "for nonzero m. Full designated tuples and full selected tables are identified before "
                    + "dependent coordinate evaluation; input construction uses the same inverse equivalences."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original33-scalar-boolean-obstruction"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion.original33_bound_and_boolean_obstruction"),
                H("The literal minimum and the attained least uniform real exponent"),
                StatementSource.FromAuthor(Original33Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "R,S are finite nonempty original labelled pair index types, and the fixed oriented skeleton "
                    + "is arbitrary. For every finite nonempty designated endpoint family and fixed onto designated "
                    + "maps, all ordinary endpoint alphabets/maps and the finite nonempty output type O and total "
                    + "outer task G vary. Each ordinary map has some surjective row and some surjective column. "
                    + "Define tau,T,D,Theta and actual labelled widths as above. Allowed(s,psi) abbreviates exactly "
                    + "these assumptions, not a width or geometry premise. The conclusion combines the same-task "
                    + "literal minimum with a fixed k,L>0,ell chosen before real alpha and C. k attains Theta, "
                    + "ell is the internally scaled actual optimal product dual, and every resulting ordinary "
                    + "family is proved allowed. For every alpha<Theta and C>0, an integer m>=2 makes "
                    + "C Wpi(F_m)^alpha<Wcn(F_m). Only k's addition block varies; all others remain fixed ignored "
                    + "Boolean XOR and F_m has scalar Boolean output. The original-width coefficient is "
                    + "card XP*card YP, independent of m, with all raw cuts bounded by that coefficient times m^L. "
                    + "The normalized lower bound is m^(L Theta). For alpha<0 use Wpi>=1, which gives "
                    + "Wpi^alpha<=1; for alpha>=0 use the positive exponent gap L(Theta-alpha). "
                    + "Thus exponent Theta is attained with coefficient D and every smaller real exponent "
                    + "fails uniformly. Empty N_k, Theta=1, singleton effective images, zero ell and modulus one "
                    + "remain in the construction; universal upper bounds also include constant tasks and "
                    + "initial/half/terminal layers. No sharp-coefficient or order-optimization claim is made."))),
                DescribeRole.Theorem))));

    private static Formula OriginalUpperStatement() => Disp(Seq(
        Forall, Sp, V("s"), Comma, V("phi"), Comma, V("G"), Comma, Sp,
        App(V("Allowed"), V("s"), V("phi")), Implies, Sp,
        App(V("L"), V("Wcn"), App(V("min"),
            Seq(V("Wpi"), Caret, Grp(V("T"))),
            Seq(V("D"), Sp, V("Wpi"), Caret, Grp(V("Theta"))))), Comma, Sp,
        App(V("BoundaryTransport"), V("s"), V("phi"), V("G")), Dot));
    private static Formula IntegerCertificateStatement() => Disp(Seq(
        Forall, Sp, V("phi"), Comma, Sp, App(V("Onto"), V("phi")), Implies, Sp,
        Exists, Sp, V("L"), InMacro, Sp, V("Nat"), Comma, V("ell"), InMacro, Sp,
        Seq(V("Nat"), Caret, Grp(V("Z"))), Comma, Sp,
        App(V("LT"), V("zero"), V("L")), Comma, Sp,
        App(V("sum"), V("z"), Sub(V("ell"), V("z"))), Eq, Seq(V("L"), Sp, V("tau")), Comma, Sp,
        Forall, Sp, V("x"), Comma, Sp,
        App(V("L"), App(V("sum"), V("z"), Sub(V("R"), V("x")), Sub(V("ell"), V("z"))), V("L")), Dot));
    private static Formula RawSignaturesStatement() => Disp(Seq(
        Forall, Sp, V("s"), Comma, V("k"), Comma, V("phi"), Comma, V("m"), Comma, V("L"), Comma, V("ell"), Comma, V("t"), Comma, Sp,
        App(V("L"), V("two"), V("m")), Comma, App(V("RowCertificate"), V("ell"), V("L")), Implies, Sp,
        Grp(Seq(App(V("L"), V("t"), V("firstk")), Implies, Sp,
            App(V("L"), App(V("kappa"), V("t")), App(V("card"), V("XP"))))), Comma, Sp,
        Grp(Seq(App(V("LT"), V("firstk"), V("t")), Comma, App(V("L"), V("t"), V("secondk")),
            Implies, Sp, App(V("L"), App(V("kappa"), V("t")),
                Seq(App(V("card"), V("XP")), Sp, V("m"), Caret, Grp(V("L")))))), Comma, Sp,
        Grp(Seq(App(V("LT"), V("secondk"), V("t")), Implies, Sp,
            App(V("L"), App(V("kappa"), V("t")),
                Seq(App(V("card"), V("XP")), Sp, App(V("card"), V("YP")), Sp,
                    V("m"), Caret, Grp(V("L")))))), Dot));
    private static Formula NormalizedInjectionStatement() => Disp(Seq(
        Forall, Sp, V("s"), Comma, V("k"), Comma, V("phi"), Comma, V("m"), Comma, V("ell"), Comma, Sp,
        App(V("Onto"), V("phi")), Implies, Sp,
        App(V("Injective"), App(V("ResponseMap"), V("lowerPrefix"))), Dot));
    private static Formula Original33Statement() => Disp(Seq(
        Forall, Sp, V("s"), Comma, V("psi"), Comma, V("G"), Comma, Sp,
        App(V("Allowed"), V("s"), V("psi")), Implies, Sp,
        App(V("L"), V("Wcn"), App(V("min"), Seq(V("Wpi"), Caret, Grp(V("T"))),
            Seq(V("D"), Sp, V("Wpi"), Caret, Grp(V("Theta"))))), Comma, Sp,
        Exists, Sp, V("k"), Comma, V("L"), Comma, V("ell"), Comma, Sp,
        App(V("LT"), V("zero"), V("L")), Comma, Sp, Sub(V("theta"), V("k")), Eq, V("Theta"), Comma, Sp,
        Grp(Seq(Forall, Sp, V("m"), Comma, App(V("FamilyAllowed"), V("k"), V("m"), V("ell")))), Comma, Sp,
        Forall, Sp, V("alpha"), Comma, V("C"), InMacro, Sp, V("Real"), Comma, Sp,
        App(V("LT"), V("alpha"), V("Theta")), Comma, App(V("LT"), V("zero"), V("C")), Implies, Sp,
        Exists, Sp, V("m"), InMacro, Sp, V("Nat"), Comma, App(V("L"), V("two"), V("m")), Comma, Sp,
        App(V("LT"), Seq(V("C"), Sp, App(V("Wpi"), Sub(V("F"), V("m"))), Caret, Grp(V("alpha"))),
            App(V("Wcn"), Sub(V("F"), V("m")))), Dot));

    private static Formula V(string name) => F.Id(name);
    private static Formula Sub(Formula value, Formula index) => Seq(value, Underscore, Grp(index));
    private static Formula App(Formula name, params Formula[] arguments) =>
        Seq(name, Open, Seq(arguments.SelectMany((argument, index) => index == 0
            ? new[] { argument } : new[] { Comma, Sp, argument }).ToArray()), Close);

    private static Formula Statement() => Disp(Seq(
        Exists, Sp, V("q"), Comma, Sp,
        Forall, Sp, V("c"), Comma, V("x"), Comma, V("z"), Comma, V("d"), Comma, Sp,
        V("z"), InMacro, Sp, Sub(V("S"), V("x")), Implies, Sp,
        Exists, Sp, V("s"), Comma, Sp,
        Forall, Sp, V("b"), InMacro, Sp, Sub(Seq(Mathcal, Grp(V("C"))), V("c")), Comma, Sp,
        App(Sub(V("R"), V("P")), App(V("q"), V("x"), V("b")), V("s")), Eq,
        App(Seq(Sub(V("H"), V("z")), Caret, Grp(V("b"))), V("d")), Dot));

    private static Formula RealExtremaStatement() => Disp(Seq(
        Exists, Sp, V("lambda"), Comma, V("w"), Comma, Sp,
        App(Sub(V("B"), V("X")), V("lambda")), Comma, Sp,
        App(V("P"), V("lambda")), Comma, Sp,
        App(Sub(V("B"), V("Z")), V("w")), Comma, Sp,
        App(V("Q"), V("w")), Comma, Sp,
        Forall, Sp, V("mu"), InMacro, Sp, Seq(V("R"), Caret, Grp(V("X"))), Comma, Sp,
        Grp(Seq(App(V("P"), V("mu")), Implies, Sp,
            App(V("L"), App(Sub(V("S"), V("X")), V("lambda")),
                App(Sub(V("S"), V("X")), V("mu"))))), Comma, Sp,
        Forall, Sp, V("v"), InMacro, Sp, Seq(V("R"), Caret, Grp(V("Z"))), Comma, Sp,
        Grp(Seq(App(V("Q"), V("v")), Implies, Sp,
            App(V("L"), App(Sub(V("S"), V("Z")), V("v")),
                App(Sub(V("S"), V("Z")), V("w"))))), Dot));

    private static Formula RealDualityStatement() => Disp(Seq(
        Exists, Sp, V("lambda"), Comma, V("w"), Comma, Sp,
        App(V("P"), V("lambda")), Comma, Sp, App(V("Q"), V("w")), Comma, Sp,
        App(Sub(V("S"), V("X")), V("lambda")), Eq, App(Sub(V("S"), V("Z")), V("w")), Comma, Sp,
        Forall, Sp, V("mu"), InMacro, Sp, Seq(V("R"), Caret, Grp(V("X"))), Comma, Sp,
        Grp(Seq(App(V("P"), V("mu")), Implies, Sp,
            App(V("L"), App(Sub(V("S"), V("X")), V("lambda")),
                App(Sub(V("S"), V("X")), V("mu"))))), Comma, Sp,
        Forall, Sp, V("v"), InMacro, Sp, Seq(V("R"), Caret, Grp(V("Z"))), Comma, Sp,
        Grp(Seq(App(V("Q"), V("v")), Implies, Sp,
            App(V("L"), App(Sub(V("S"), V("Z")), V("v")),
                App(Sub(V("S"), V("Z")), V("w"))))), Dot));
    private static Formula ActiveStatement() => Disp(Seq(
        Forall, Sp, V("d"), InMacro, Sp, Seq(V("R"), Caret, Grp(V("I"))), Comma, Sp,
        Grp(Seq(Forall, Sp, V("j"), Comma, Sp, App(V("Active"), V("v"), V("j")), Implies, Sp,
            App(Sub(V("a"),V("j")),V("d")), Eq, V("zero"))), Implies, Sp, V("d"), Eq, V("zero"), Dot));


    private static Formula RationalExtremeStatement() => Disp(Seq(
        Forall, Sp, V("A"), InMacro, Sp, App(V("Matrix"), V("J"), V("I"), V("Q")), Comma, Sp,
        V("b"), InMacro, Sp, Seq(V("Q"), Caret, Grp(V("J"))), Comma, Sp,
        Forall, Sp, V("v"), InMacro, Sp,
        App(V("Extreme"), App(V("K"), V("A"), V("b"))), Comma, Sp,
        Exists, Sp, V("q"), InMacro, Sp, Seq(V("Q"), Caret, Grp(V("I"))), Comma, Sp,
        App(Sub(V("C"), V("I")), V("q")), Eq, V("v"), Dot));

    private static Formula RationalDualityStatement() => Disp(Seq(
        Exists, Sp, V("lambda"), InMacro, Sp, Seq(V("Q"), Caret, Grp(V("X"))), Comma, Sp,
        V("w"), InMacro, Sp, Seq(V("Q"), Caret, Grp(V("Z"))), Comma, Sp,
        App(Sub(V("P"), V("Q")), V("lambda")), Comma, Sp,
        App(Sub(V("Q"), V("Q")), V("w")), Comma, Sp,
        App(Sub(V("S"), V("X")), V("lambda")), Eq,
        App(Sub(V("S"), V("Z")), V("w")), Comma, Sp,
        Forall, Sp, V("mu"), InMacro, Sp, Seq(V("R"), Caret, Grp(V("X"))), Comma, Sp,
        Grp(Seq(App(V("P"), V("mu")), Implies, Sp,
            App(V("L"), App(Sub(V("S"), V("X")), App(Sub(V("C"), V("X")), V("lambda"))),
                App(Sub(V("S"), V("X")), V("mu"))))), Comma, Sp,
        Forall, Sp, V("v"), InMacro, Sp, Seq(V("R"), Caret, Grp(V("Z"))), Comma, Sp,
        Grp(Seq(App(V("Q"), V("v")), Implies, Sp,
            App(V("L"), App(Sub(V("S"), V("Z")), V("v")),
                App(Sub(V("S"), V("Z")), App(Sub(V("C"), V("Z")), V("w")))))), Dot));

    private static Formula FractionalCoverStatement() => Disp(Seq(
        Forall, Sp, V("H"), Comma, V("U"), Comma, V("S"), Comma, V("w"), Comma, Sp,
        App(V("SubmodularCoverAssumptions"), V("H"), V("U"), V("S"), V("w")), Implies, Sp,
        App(V("L"), App(V("H"), V("U")),
            App(V("sum"), V("r"), Seq(Sub(V("w"), V("r")), App(V("H"), Sub(V("S"), V("r")))))), Dot));

    private static Formula WeightedEntropyStatement() => Disp(Seq(
        Forall, Sp, V("p"), Comma, V("u"), Comma, V("S"), Comma, V("w"), Comma, Sp,
        App(V("LawAndCover"), V("p"), V("S"), V("w")), Implies, Sp,
        App(V("L"), App(Sub(V("H"), V("p")), V("A")),
            App(V("sum"), V("r"), Seq(Sub(V("w"), V("r")), App(Sub(V("H"), V("p")), Sub(V("S"), V("r")))))), Dot));

    private static Formula RelationLogStatement() => Disp(Seq(
        Forall, Sp, V("H"), Comma, V("S"), Comma, V("w"), Comma, Sp,
        App(V("Cover"), V("S"), V("w")), Implies, Sp,
        App(V("L"), App(V("log"), App(V("N"), V("H"))),
            App(V("sum"), V("r"), Seq(Sub(V("w"), V("r")), App(V("log"), App(Sub(V("P"), V("r")), V("H")))))), Dot));

    private static Formula GroupedBoundStatement() => Disp(Seq(
        Forall, Sp, V("phi"), Comma, V("G"), Comma, V("B"), Comma, V("P"), Comma, V("c"), Comma, V("w"), Comma, Sp,
        App(V("ReplayAndCover"), V("phi"), V("B"), V("P"), V("w")), Implies, Sp,
        App(V("L"), Sub(V("K"), V("c")),
            Seq(V("kappaP"), Caret, Grp(App(V("sum"), V("x"), Sub(V("w"), V("x")))))), Dot));
    private static Formula GroupedOptimalStatement() => Disp(Seq(
        Forall, Sp, V("phi"), Comma, V("G"), Comma, V("B"), Comma, V("P"), Comma, V("c"), Comma, Sp,
        App(V("ReplayPremises"), V("phi"), V("B"), V("P")), Implies, Sp,
        App(V("L"), Sub(V("K"), V("c")),
            Seq(V("kappaP"), Caret, Grp(App(V("product"), V("i"), V("E"), Sub(V("tau"), V("i")))))), Dot));
    private static Formula WholeCutStatement() => Disp(Seq(
        Forall, Sp, V("phi"), Comma, V("G"), Comma, V("B"), Comma, V("P"), Comma, Sp,
        App(V("ReplayPremises"), V("phi"), V("B"), V("P")), Implies, Sp,
        App(V("L"), V("kappaB"), Seq(App(V("d"), V("B"), V("P")),
            V("kappaP"), Caret, Grp(App(V("product"), V("i"), V("E"), Sub(V("tau"), V("i")))))), Dot));
}
