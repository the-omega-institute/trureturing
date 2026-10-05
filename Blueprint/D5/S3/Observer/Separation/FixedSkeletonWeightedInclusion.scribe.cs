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

}
