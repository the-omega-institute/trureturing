using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class UltrametricCenterSphereOrdersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/UltrametricCenterSphereOrders.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A divisor recurrence gives exactly all orders of finite nonempty ultrametrics with prescribed central radii and pointwise sphere counts, including realizations for every prescribed pair in every gap.",
        H("Complete classification of prescribed central sphere counts"),
        Blocks(
            Paragraph(Text("The central-graph edge comparison is the separate result "),
                Ref("D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges.result"),
                Text(". The classification below concerns pointwise sphere counts at every radius in the distance center.")),
            Paragraph(Text("The center throughout is the existing distance-center predicate "),
                Ref("D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges.center"),
                Text(". It consists of the nonnegative radii attained from every point; witnesses may depend on the point. No replacement notion of center is used. The classification quantifies over arbitrary natural h and n, real-valued radii c on the naturals, and natural-valued counts b. The required initial radius and strict increases are "),
                Math(In(Seq(Call("c", D(0)), Sp, Eq, Sp, D(0), Comma, Sp, Forall, Sp, F.Id("i"), Sp, Lt, Sp,
                    F.Id("h"), Comma, Sp, Call("c", F.Id("i")), Sp, Lt, Sp, Call("c", Seq(F.Id("i"), Plus, D(1)))))),
                Text(". When positivity of counts is assumed it means every index through h, including zero.")),
            Describe.Remark(DescribeId.Create("positive-sums"), DeclarationHandle.Create(Prefix + "PositiveSum"),
                H("Nonempty finite sums with repetition"), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("PositiveSum A t means that there are a natural k and a list indexed by Fin (k + 1), all of whose entries belong to A, and whose sum is t. Repeated summands are allowed. This definition does not insert a zero-length sum.")))),
            Describe.Lean(DescribeId.Create("order-recurrence"), DeclarationHandle.Create(Prefix + "orders"),
                H("The recursive candidate orders"), StatementSource.FromAuthor(Disp(Seq(
                    Call("orders", F.Id("b"), D(0)), Sp, Eq, Sp, OpenBrace, D(1), CloseBrace, Comma, Sp,
                    Call("orders", F.Id("b"), Seq(F.Id("i"), Plus, D(1))), Sp, Eq, Sp,
                    OpenBrace, F.Id("n"), Sp, Mid, Sp, Exists, Sp, F.Id("t"), Comma, Sp,
                    Call("PositiveSum", Call("orders", F.Id("b"), F.Id("i")), F.Id("t")), Sp, Land, Sp,
                    F.Id("t"), Sp, Mid, Sp, BNext(), Sp, Land, Sp,
                    F.Id("n"), Sp, Eq, Sp, BNext(), Plus, F.Id("t"), CloseBrace))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The divisibility symbol uses natural-number divisibility. These sets depend only on the count sequence. Their elements are positive by "),
                    Ref(Prefix + "orders_pos"), Text(". The recurrence itself is defined even without the positivity hypotheses later imposed by the existence classification."))), DescribeRole.Definition),
            Node("bounded-divisor-search", "A positive count bounds every sum to be checked", "mem_orders_succ_iff_bounded",
                Disp(Seq(F.Id("n"), Sp, InMacro, Sp, Call("orders", F.Id("b"), Seq(F.Id("i"), Plus, D(1))),
                    Sp, Iff, Sp, Exists, Sp, F.Id("t"), Comma, Sp, D(0), Sp, Lt, Sp, F.Id("t"), Sp, Land, Sp,
                    F.Id("t"), Sp, Leq, Sp, BNext(), Sp, Land, Sp,
                    Call("PositiveSum", Call("orders", F.Id("b"), F.Id("i")), F.Id("t")), Sp, Land, Sp,
                    F.Id("t"), Sp, Mid, Sp, BNext(), Sp, Land, Sp, F.Id("n"), Sp, Eq, Sp, BNext(), Plus, F.Id("t"))),
                "For arbitrary b, i and n, assume the count at i + 1 is positive. Then the recurrence is equivalent to the bounded search displayed here. This is a general bound on the recurrence, rather than an enumeration of a fixed example."),
            Node("closed-ball-orders", "Each prescribed closed ball has an order in the recurrence", "closedBall_order",
                Disp(Seq(Call("card", Call("closedBall", F.Id("x"), Call("c", F.Id("h")))), Sp, InMacro, Sp,
                    Call("orders", F.Id("b"), F.Id("h")))),
                "Let X be any finite metric space with IsUltrametricDist, and let x be any point of X. Assume the initial radius and strict increases stated above and that, at every prescribed radius through h, the sphere about every point has the prescribed count. Then the displayed membership holds. This theorem does not assume the center equality or positivity of b. Lower closed balls partition a strict upper ball by lower_closedBalls; closedBall_card_eq separates its sphere from its strict ball."),
            Node("necessity", "Every realization has initial count one and an order in the recurrence", "necessary",
                Disp(Seq(Call("b", D(0)), Sp, Eq, Sp, D(1), Sp, Land, Sp, Call("card", F.Id("X")),
                    Sp, InMacro, Sp, Call("orders", F.Id("b"), F.Id("h")))),
                "For any finite nonempty ultrametric X, assume the initial radius and strict increases, center X exactly the image of c on the indices through h, and every prescribed pointwise sphere count. Then the displayed criterion holds. Necessity imposes no restriction on other distance values and does not separately assume positive counts. It includes h equal to zero: the finite nonempty space is then a singleton."),
            Describe.Remark(DescribeId.Create("realization-contract"), DeclarationHandle.Create(Prefix + "Model"),
                H("A realization retains the entire center, count and support contract"), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Model c b u v h n contains a carrier with MetricSpace, IsUltrametricDist, Finite and Nonempty instances; its Nat.card is n; its original distance center is exactly the prescribed radii through h; and every pointwise sphere count at every such radius equals b. Its distance field restricts all distances to allowed c u v h.")),
                    Paragraph(Text("The allowed set is the union of the central radii through h and the values of u and v at indices strictly below h, as defined by "),
                        Ref(Prefix + "allowed"), Text(". For every gap these two auxiliary radii are fixed in advance and satisfy "),
                        Math(In(Seq(Forall, Sp, F.Id("i"), Sp, Lt, Sp, F.Id("h"), Comma, Sp,
                            Call("c", F.Id("i")), Sp, Lt, Sp, Call("u", F.Id("i")), Sp, Lt, Sp,
                            Call("v", F.Id("i")), Sp, Lt, Sp, Call("c", Seq(F.Id("i"), Plus, D(1)))))),
                        Text(". The contract bounds the support; it does not require every allowed auxiliary value to occur.")))),
            Node("sufficiency", "Every candidate order is realized for every prescribed pair in every gap", "sufficient",
                Disp(Seq(Criterion(), Sp, Rightarrow, Sp, Realization())),
                "Assume the initial radius, strict increases, every prescribed gap inequality just stated, and positive counts through h. If the initial count is one and n belongs to orders b h, then Model c b u v h n is nonempty. The auxiliary sequences u and v are arbitrary subject to those inequalities. The construction begins at a singleton and forms groups of lower-level models; one group is joined at the first auxiliary radius, the other groups at the second, and the groups at the next central radius. This prevents either newly introduced auxiliary radius from becoming central."),
            Node("prescribed-support-iff", "The exact criterion holds with arbitrary prescribed auxiliary pairs", "possible_orders_iff",
                Disp(Seq(Realization(), Sp, Iff, Sp, Criterion())),
                "Assume the initial radius, strict increases, every prescribed gap inequality, and positive counts through h. For every n the displayed equivalence is exact. Model contains all the metric, finiteness, nonemptiness, order, original center, pointwise count and distance-support requirements; none is dropped. If b at zero differs from one, the right side is false and no such Model exists."),
            Node("unrestricted-iff", "The same recurrence classifies all realizations without a distance-support restriction", "possible_orders_unrestricted_iff",
                Disp(Seq(Open, Exists, Sp, F.Id("X"), Colon, F.Id("Type"), Comma, Sp,
                    Exists, Sp, F.Id("m"), Colon, Call("MetricSpace", F.Id("X")), Comma, Sp,
                    Call("IsUltrametricDist", F.Id("X")), Sp, Land, Sp, Call("Finite", F.Id("X")), Sp, Land, Sp,
                    Call("Nonempty", F.Id("X")), Sp, Land, Sp, Call("card", F.Id("X")), Sp, Eq, Sp, F.Id("n"),
                    Sp, Land, Sp, Call("center", F.Id("X")), Sp, Eq, Sp, Call("image", F.Id("c"), Call("Iic", F.Id("h"))),
                    Sp, Land, Sp, Forall, Sp, F.Id("i"), Sp, Leq, Sp, F.Id("h"), Comma, Sp,
                    Forall, Sp, F.Id("x"), Colon, F.Id("X"), Comma, Sp,
                    Call("card", Call("sphere", F.Id("x"), Call("c", F.Id("i")))), Sp, Eq, Sp, Call("b", F.Id("i")),
                    Close, Sp, Iff, Sp, Open, Criterion(), Close)),
                "Assume only the initial radius, strict increases and positive counts through h. The left side existentially chooses a carrier and its metric; all other structures and sphere counts refer to that same chosen metric. There is no hypothesis restricting the remaining distances. The converse chooses one-third and two-thirds of each prescribed gap and applies the stronger construction. This is the unrestricted existence iff, including the initial-count obstruction and the singleton boundary."))));

    private static DocumentBlock Node(string id, string title, string name, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula BNext() => Call("b", Seq(F.Id("i"), Plus, D(1)));
    private static Formula Criterion() => Seq(Call("b", D(0)), Sp, Eq, Sp, D(1), Sp, Land, Sp,
        F.Id("n"), Sp, InMacro, Sp, Call("orders", F.Id("b"), F.Id("h")));
    private static Formula Realization() => Call("Nonempty", Call("Model", F.Id("c"), F.Id("b"),
        F.Id("u"), F.Id("v"), F.Id("h"), F.Id("n")));
}
