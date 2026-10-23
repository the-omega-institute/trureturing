using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class PresburgerFiniteFamiliesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite dependent products and chart unions preserve polynomial finite trace bounds.",
        H("Finite Families of Integer Trace Relations"),
        Blocks(
            Paragraph(Text(
                "Let K and T be finite index types, X(k) arbitrary source carriers and Y(t) "
                + "arbitrary descriptor carriers. For each k,t, the relation f(k,t) takes "
                + "one source and one descriptor to Bool. The joint relation evaluates on "
                + "the disjoint unions Sigma X and Sigma Y using their tags. A finite sample "
                + "may repeat descriptor values and may use only some types. None of K, T, "
                + "X(k), or Y(t) is required to be inhabited.")),
            Describe.Lean(
                DescribeId.Create("dependent-descriptor-trace-product"),
                Handle("trace_card_dependent_product"),
                H("Restriction to descriptor types gives a product upper bound"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("card", Call("Tr", F.Id("jointSample"))), Sp, Le, Sp,
                    Call("prod", F.Id("t"), Call("card", Call("Tr", F.Id("slice"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "With one common source carrier X, put I(t)={i : sample(i).tag=t}. "
                    + "The descriptor at i transports along this equality into Y(t). "
                    + "Code each source by its tuple of Boolean restrictions to I(t). All "
                    + "restrictions belong to their respective trace families, using the "
                    + "same source. A decoder recovers every coordinate by taking t to be "
                    + "that coordinate's sample tag. The finite source-code bound applies, "
                    + "and the code type has the product of the component cardinalities. "
                    + "This bounds global patterns. It does not assert that arbitrary traces have "
                    + "a common source. Empty Y(t) requires no padding descriptor."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-chart-trace-sum"),
                Handle("trace_card_chart_sum"),
                H("A union of source charts has a sum upper bound"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("card", Call("Tr", F.Id("SigmaX"))), Sp, Le, Sp,
                    Call("sum", F.Id("k"), Call("card", Call("Tr", F.Id("Xk"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every trace on the disjoint union of source charts has a source in "
                    + "one chart. It therefore lies in the union of that chart's trace "
                    + "family. The cardinality of a finite union is at most the sum of "
                    + "the cardinalities, even when different charts give the same trace. "
                    + "An empty chart index type gives an empty source union."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-chart-type-polynomial-bound"),
                Handle("finite_family_polynomial_bound"),
                H("One fixed positive polynomial bounds every finite sample"),
                StatementSource.FromAuthor(Disp(Seq(
                    D(0), Lt, F.Id("Ctotal"), Sp, Land, Sp,
                    Call("card", Call("Tr", F.Id("jointSample"))), Sp, Le, Sp,
                    F.Id("Ctotal"), Cdot, Open, F.Id("n"), Plus, D(1), Close,
                    Caret, Grp(F.Id("stotal"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume Growth(f(k,t),C(k,t),s(k,t)) for every pair of tags. Define "
                    + "C_total=1+sum_k prod_t C(k,t) and s_total=sum_k sum_t s(k,t). "
                    + "For each chart the product bound uses card(I(t))<=n, multiplies "
                    + "coefficients, and adds exponents. The chart sum is bounded using "
                    + "each chart exponent's inequality with s_total and n+1>=1. Adding "
                    + "one to the coefficient makes it positive even when K is empty. "
                    + "These constants depend on the finite family, independently of "
                    + "the size, repetitions, or values of the finite sample."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-exponential-polynomial-domination"),
                Handle("finite_exponential_domination"),
                H("An explicit exponential value exceeds any natural polynomial budget"),
                StatementSource.FromAuthor(Disp(Seq(
                    Exists, Sp, F.Id("n"), Comma, Sp,
                    F.Id("C"), Cdot, Open, F.Id("n"), Plus, D(1), Close,
                    Caret, Grp(F.Id("s")), Sp, Lt, Sp, D(2), Caret, Grp(F.Id("n"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For arbitrary natural C,s, take k=C*(s+2)^s+1 and n=(s+1)*k. "
                    + "Then n+1<=(s+2)*k and C*(n+1)^s<=C*(s+2)^s*k^s "
                    + "<k^(s+1)<=(2^k)^(s+1)=2^n. The strict step uses "
                    + "C*(s+2)^s<k; the final bound uses Nat.lt_two_pow_self. "
                    + "The construction includes C=0 and s=0."))),
                DescribeRole.Theorem))));

    private static DeclarationHandle Handle(string name) => DeclarationHandle.Create(
        "D5/S0/Computability/PresburgerFiniteFamilies." + name);
}
