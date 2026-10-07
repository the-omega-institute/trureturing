using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Separation.FixedSkeletonWeightedInclusion;

internal sealed class LabelledResponsesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The same labelled task admits a common suffix replay, same-law coordinate entropy and completion sorting.",
        H("Labelled Responses and Completion Geometry"),
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
                    "D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion/LabelledResponses.nonnested_common_suffix_replay"),
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
                DescribeId.Create("fractional-submodular-cover"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion/LabelledResponses.fractional_submodular_cover"),
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
                DeclarationHandle.Create("D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion/LabelledResponses.weighted_coordinate_entropy"),
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
                DescribeRole.Theorem))));

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
}
