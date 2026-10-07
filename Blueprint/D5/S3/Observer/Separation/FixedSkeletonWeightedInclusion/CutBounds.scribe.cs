using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Separation.FixedSkeletonWeightedInclusion;

internal sealed class CutBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual restriction images and grouped responses give every labelled layer the original literal minimum.",
        H("Actual Same-Task Cut Bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fractional-relation-log-bound"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion/CutBounds.fractional_relation_log_bound"),
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
                DeclarationHandle.Create("D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion/CutBounds.grouped_response_bound"),
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
                DeclarationHandle.Create("D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion/CutBounds.grouped_optimal_product_bound"),
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
                DeclarationHandle.Create("D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion/CutBounds.nonnested_cut_product_bound"),
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
                DeclarationHandle.Create("D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion/CutBounds.original_labelled_upper_contract"),
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
                DescribeRole.Theorem))));

    private static Formula OriginalUpperStatement() => Disp(Seq(
        Forall, Sp, V("s"), Comma, V("phi"), Comma, V("G"), Comma, Sp,
        App(V("Allowed"), V("s"), V("phi")), Implies, Sp,
        App(V("L"), V("Wcn"), App(V("min"),
            Seq(V("Wpi"), Caret, Grp(V("T"))),
            Seq(V("D"), Sp, V("Wpi"), Caret, Grp(V("Theta"))))), Comma, Sp,
        App(V("BoundaryTransport"), V("s"), V("phi"), V("G")), Dot));

    private static Formula V(string name) => F.Id(name);

    private static Formula Sub(Formula value, Formula index) => Seq(value, Underscore, Grp(index));

    private static Formula App(Formula name, params Formula[] arguments) =>
        Seq(name, Open, Seq(arguments.SelectMany((argument, index) => index == 0
            ? new[] { argument } : new[] { Comma, Sp, argument }).ToArray()), Close);

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
