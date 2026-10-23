using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class ScalarFidelityEndpointDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/ScalarFidelityEndpoint.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/rajaei2026generalized");
    private static Formula V(string name) => F.Id(name);
    private static Formula Sq(string name) => Seq(V(name), Caret, Grp(D(2)));
    private static Formula Quotient(string a, string b, string c) =>
        Call("g", V(a), V(b), V(c));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A sharp scalar condition characterizes dominance of the fidelity quotient "
        + "over every independent upper endpoint in the unit cube.",
        H("Sharp Scalar Fidelity Endpoint Comparison"),
        Blocks(
            Describe.Lean(DescribeId.Create("scalar-fidelity-quotient"),
                DeclarationHandle.Create(Prefix + "scalarQuotient"),
                H("The scalar quotient"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, V("a"), Comma, V("b"), Comma, V("c"), Sp,
                    InMacro, Sp, Mathbb, Grp(V("R")), Comma, Quad,
                    Quotient("a", "b", "c"), Eq,
                    Frac, Grp(Sq("a"), Plus, Sq("b"), Plus, Sq("c"), Minus, D(1)),
                    Grp(D(2), V("a"), V("b"))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For real a,b,c, scalarQuotient(a,b,c), denoted by g(a,b,c), "
                    + "is (a squared+b squared+c squared-1)/(2ab). The theorem uses "
                    + "strictly positive a and b, so its denominators are positive. "
                    + "Rajaei's qubit identity motivates this scalar expression; "
                    + "the scalar definition itself imposes no matrix realization."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("scalar-fidelity-sharp-endpoint"),
                DeclarationHandle.Create(Prefix + "lower_corner_dominance_iff"),
                H("Exact lower-corner dominance"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, V("a"), Comma, V("b"), Comma, V("c"), Sp,
                    InMacro, Sp, Mathbb, Grp(V("R")), Comma, Quad,
                    D(0), Lt, V("a"), Le, D(1), Comma, Esc,
                    D(0), Lt, V("b"), Le, D(1), Comma, Esc,
                    D(0), Le, Sp, V("c"), Le, D(1), Sp, Rightarrow, Sp,
                    Open, Open, Forall, Sp, V("A"), Comma, V("B"), Comma, V("C"), Sp,
                    InMacro, Sp, Mathbb, Grp(V("R")), Comma, Esc,
                    V("a"), Le, Sp, V("A"), Le, D(1), Sp, Land, Sp,
                    V("b"), Le, Sp, V("B"), Le, D(1), Sp, Land, Sp,
                    V("c"), Le, Sp, V("C"), Le, D(1), Sp, Rightarrow, Sp,
                    Quotient("a", "b", "c"), Le, Quotient("A", "B", "C"), Close,
                    Sp, Leftrightarrow, Sp,
                    new Formula.Absolute(Seq(Sq("a"), Minus, Sq("b"))),
                    Le, D(1), Minus, Sq("c"), Close))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For every base point with 0<a,b<=1 and 0<=c<=1, the displayed "
                        + "equivalence includes both directions and all closed upper endpoints. "
                        + "The upper endpoints vary independently. Neither the endpoint nor "
                        + "any intervening point is required to satisfy the squared-imbalance "
                        + "condition. The sharp scalar argument is due to Haobo Ma and "
                        + "Wenlin Zhang in their corrected note, Monotonicity of the qubit "
                        + "fidelity quotient and fixed-reference convexity. Rajaei's "
                        + "Corollaries 5 and 6 supply the earlier sufficient criteria.")),
                    Paragraph(Text(
                        "For sufficiency put d=1-c squared, x=A-a and y=B-b. Clearing "
                        + "the positive denominators gives the nonnegative expression below. "
                        + "The condition bounds both signed squared differences by d and "
                        + "also bounds (a-b) squared by d. Increasing c to C adds a "
                        + "nonnegative contribution because 0<=c<=C.")),
                    Paragraph(Math(Disp(Seq(
                        Forall, Sp, V("a"), Comma, V("b"), Comma, V("c"), Comma,
                        V("A"), Comma, V("B"), Comma, V("x"), Comma, V("y"), Comma, V("d"), Sp,
                        InMacro, Sp, Mathbb, Grp(V("R")), Comma, Quad,
                        Open, V("x"), Eq, V("A"), Minus, V("a"), Sp, Land, Sp,
                        V("y"), Eq, V("B"), Minus, V("b"), Sp, Land, Sp,
                        V("d"), Eq, D(1), Minus, Sq("c"), Close, Sp, Rightarrow, Sp,
                        V("a"), V("b"), Open, Sq("A"), Plus, Sq("B"), Plus, Sq("c"), Minus, D(1), Close,
                        Minus, V("A"), V("B"), Open, Sq("a"), Plus, Sq("b"), Plus, Sq("c"), Minus, D(1), Close,
                        Eq, V("b"), V("x"), Open, Sq("a"), Minus, Sq("b"), Plus, V("d"), Close,
                        Plus, V("a"), V("y"), Open, Sq("b"), Minus, Sq("a"), Plus, V("d"), Close,
                        Plus, V("a"), V("b"), Open, V("x"), Minus, V("y"), Close, Caret, Grp(D(2)),
                        Plus, Open, V("d"), Minus, Open, V("a"), Minus, V("b"), Close,
                        Caret, Grp(D(2)), Close, V("x"), V("y"))))),
                    Paragraph(Text(
                        "For necessity, if b squared-a squared exceeds 1-c squared, "
                        + "choose s=sqrt(b squared+c squared-1). Then a<s<=1, and the "
                        + "difference after increasing a to s has numerator "
                        + "-bs(s-a) squared after multiplication by positive denominators. "
                        + "It is strictly negative. Interchanging a and b gives the other "
                        + "signed bound. This proves the sharpness at the lower corner, "
                        + "including c=0 and c=1. It does not characterize physical channel "
                        + "realizability, prove a matrix fidelity bridge, or classify CPTP maps."))),
                DescribeRole.Theorem))));
}
