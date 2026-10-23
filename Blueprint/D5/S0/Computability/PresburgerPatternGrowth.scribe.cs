using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class PresburgerPatternGrowthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Separated integer thresholds and fixed-modulus atoms have polynomial finite trace growth.",
        H("Finite Traces of Separated Integer Atoms"),
        Blocks(
            Paragraph(Text(
                "For an arbitrary source carrier X and a finite index carrier I of size n, "
                + "Tr(f) is the finite set of Boolean functions p on I for which one source "
                + "x satisfies f(x,i)=p(i) at every index. A sample map I to Y may repeat "
                + "descriptor values. Neither X nor the map into its numeric coordinates "
                + "is assumed finite, definable, injective, or inhabited.")),
            Describe.Lean(
                DescribeId.Create("finite-trace-membership"),
                Handle("mem_traces"),
                H("A trace is realized by one common source"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("p"), Sp, F.Id("in"), Sp, Call("Tr", F.Id("f")), Sp, Iff, Sp,
                    Exists, Sp, F.Id("x"), Comma, Sp, Call("f", F.Id("x")), Eq, F.Id("p")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Membership in Tr(f) means that one source x realizes the entire Boolean "
                    + "pattern p. Equality of functions enforces every sample coordinate at once. "
                    + "The finite index type may be empty; the source carrier need not have "
                    + "an inhabitant. This equivalence supplies witnesses for the finite-code "
                    + "and dependent-family counting arguments."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-source-code-trace-count"),
                Handle("trace_card_factor"),
                H("A finite source code bounds the number of traces"),
                StatementSource.FromAuthor(Bound(F.Id("f"), Call("card", F.Id("K")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Suppose K is finite and every source pattern factors as "
                    + "f(x)=decode(code(x)) for maps code:X to K and decode:K to Bool^I. "
                    + "Every witnessed trace then lies in the image of decode on K. "
                    + "The finite image bound gives at most card(K) traces. The source "
                    + "carrier may be infinite or empty, and code need not be injective "
                    + "or surjective. Residue codes and tuples of descriptor-type "
                    + "restrictions are two applications."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("separated-threshold-trace-count"),
                Handle("trace_card_threshold"),
                H("Threshold patterns are counted by their number of true coordinates"),
                StatementSource.FromAuthor(Bound(Call("threshold", F.Id("A"), F.Id("B")),
                    Seq(F.Id("n"), Plus, D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The threshold is A(x) <= B(i), with arbitrary integer functions A and B. "
                    + "For any two sources the corresponding truth sets are nested, by total "
                    + "order of their A values. Equal cardinalities force equal nested "
                    + "finsets, using Finset.eq_of_subset_of_card_le. Cardinality therefore "
                    + "injects the realized patterns into the n+1 possible integers from "
                    + "zero through n. This is the substantive counting step; ties, constant "
                    + "functions, and the empty sample remain covered."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("separated-divisibility-trace-count"),
                Handle("trace_card_dvd"),
                H("Divisibility patterns factor through a finite source residue"),
                StatementSource.FromAuthor(Bound(Call("dvd", F.Id("d"), F.Id("A"), F.Id("B")),
                    F.Id("d"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a fixed positive natural modulus d, the atom is d divides A(x)+B(i). "
                    + "The source code is the nonnegative integer remainder A(x) modulo d, "
                    + "viewed as Fin d. Existing integer remainder identities and the "
                    + "Finset image cardinality bound supply at most d patterns, independently "
                    + "of the number and values of sample coordinates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("separated-negated-divisibility-trace-count"),
                Handle("trace_card_ndvd"),
                H("Negated divisibility has the same fixed-modulus bound"),
                StatementSource.FromAuthor(Bound(Call("ndvd", F.Id("d"), F.Id("A"), F.Id("B")),
                    F.Id("d"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The atom is the negation of d divides A(x)+B(i), still with d positive. "
                    + "Apply Boolean negation to each divisibility pattern. The unary "
                    + "image bound cannot increase its cardinality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unary-boolean-trace-count"),
                Handle("trace_card_unary"),
                H("A unary Boolean operation does not increase trace count"),
                StatementSource.FromAuthor(Bound(Call("unary", F.Id("u"), F.Id("f")),
                    Card(F.Id("f")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every realized unary pattern is the image of the input pattern "
                    + "witnessed by the same source. Finset.card_image_le gives the bound "
                    + "for any Bool to Bool operation, including negation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("binary-boolean-trace-product-count"),
                Handle("trace_card_binary"),
                H("A binary Boolean operation has a product upper bound"),
                StatementSource.FromAuthor(Bound(Call("binary", F.Id("v"), F.Id("f"), F.Id("g")),
                    Seq(Card(F.Id("f")), Cdot, Card(F.Id("g"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any Bool to Bool to Bool operation, each realized output uses "
                    + "one pair of input traces. Its image lies in the image of their "
                    + "Cartesian product, so Finset.card_image2_le gives the product bound. "
                    + "The source witness is shared in the actual output trace; forgetting "
                    + "compatibility enlarges only the upper-bound family. There is no "
                    + "assertion that every pair is jointly attainable. Intersection and "
                    + "union are immediate choices of the operation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("separated-atom-polynomial-trace-bound"),
                Handle("polynomial_trace_bound"),
                H("Finite Boolean compositions have a fixed positive polynomial budget"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("Growth", F.Id("f"), F.Id("C"), F.Id("s")), Sp, Rightarrow, Sp,
                    D(0), Lt, F.Id("C"), Sp, Land, Sp,
                    Forall, Sp, F.Id("I"), Comma, Sp, F.Id("y"), Colon, F.Id("I"), To, Sp,
                    F.Id("Y"), Comma, Sp,
                    Card(Call("sample", F.Id("f"), F.Id("y"))), Sp, Le, Sp,
                    F.Id("C"), Cdot, Open, F.Id("n"), Plus, D(1), Close,
                    Caret, Grp(F.Id("s"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Computability/aschenbrenner2011vcdensity")),
                Blocks(
                    Paragraph(Text(
                        "Growth(f,C,s) is an exact semantic derivation from constants, "
                        + "separated thresholds, and fixed positive-modulus divisibility "
                        + "or its negation, closed under arbitrary unary and binary Boolean "
                        + "operations. It does not assume a trace bound. Constants have "
                        + "budget (1,0), thresholds (1,1), and modulus-d atoms (d,0). "
                        + "Unary operations preserve the budget; binary operations multiply "
                        + "coefficients and add exponents. Induction proves positivity of "
                        + "C and the uniform C*(n+1)^s bound for every finite sample map.")),
                    Paragraph(Text(
                        "The hypotheses concern separated integer atoms and their finite "
                        + "Boolean compositions. They do not impose any bound on the source "
                        + "values or on the samples, and do not assert that a quantified "
                        + "formula has such a derivation. The finite trace viewpoint is "
                        + "consistent with the literature context of Aschenbrenner, Dolich, "
                        + "Haskell, Macpherson, and Starchenko, arXiv:1109.5438."))),
                DescribeRole.Theorem))));

    private static DeclarationHandle Handle(string name) => DeclarationHandle.Create(
        "D5/S0/Computability/PresburgerPatternGrowth." + name);

    private static Formula Card(Formula f) => Call("card", Call("Tr", f));

    private static Formula Bound(Formula f, Formula upper) =>
        Disp(Seq(Card(f), Sp, Le, Sp, upper));
}
