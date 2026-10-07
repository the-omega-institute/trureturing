using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Separation.FixedSkeletonWeightedInclusion;

internal sealed class RowCertificatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual row-image linear programs have attained real and rational certificates.",
        H("Attained Row-Image Certificates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("row-image-real-extrema"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion/RowCertificates.row_image_real_extrema"),
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
                    "D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion/RowCertificates.row_image_real_duality"),
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
                DeclarationHandle.Create("D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion/RowCertificates.active_constraint_kernel_zero"),
                H("Original active normals determine an extreme point"),
                StatementSource.FromAuthor(ActiveStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For finite coordinate and constraint types I,J, let a_j be real linear functionals, b_j real constants, and K={u: forall j, a_j(u)<=b_j}. Let v be an extreme point of K. Active(v,j) means a_j(v)=b_j. A real direction d vanishes whenever every original active normal evaluates to zero on d. The identifier zero denotes the zero scalar or vector. Inactive slacks provide one positive finite perturbation radius. Both v plus and minus epsilon d remain feasible, and their midpoint is v; extremality forces d=0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rational-extreme-point"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion/RowCertificates.rational_extreme_point"),
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
                DeclarationHandle.Create("D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion/RowCertificates.row_image_rational_duality"),
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
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);

    private static Formula Sub(Formula value, Formula index) => Seq(value, Underscore, Grp(index));

    private static Formula App(Formula name, params Formula[] arguments) =>
        Seq(name, Open, Seq(arguments.SelectMany((argument, index) => index == 0
            ? new[] { argument } : new[] { Comma, Sp, argument }).ToArray()), Close);

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
}
