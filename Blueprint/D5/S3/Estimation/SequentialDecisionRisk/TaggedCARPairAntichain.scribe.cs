using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.SequentialDecisionRisk;

internal sealed class TaggedCARPairAntichainDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Estimation/SequentialDecisionRisk/TaggedCARPairAntichain.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal pair masses force equality of tagged CAR profiles under a common stochastic simulation.",
        H("Fixed Pair Profiles and Tagged CAR Antichains"),
        Blocks(
            Paragraph(Text("Let Q and K be finite types, with decidable equality on K, and let A(q) be a finite subset of K for each readout q. The actual rows are the dependent pairs (q,i) with i in A(q). The output alphabet O consists of every tagged nonempty subset (q,B) with B contained in A(q), including outputs of weight zero. Fibers A(q) may be empty; they then contribute neither rows nor outputs.")),
            Paragraph(Text("Write I(q,i,B) for the incidence relation saying that the tag of B is q and its underlying subset contains i. A CAR profile w assigns a nonnegative real weight to every B in O and satisfies sum over B of 1[I(q,i,B)] w(B) = 1 for every actual i in A(q). Its row is W_w((q,i),B) = 1[I(q,i,B)] w(B). Define r_w(q,i,j) as the sum of w(B) over outputs incident to both (q,i) and (q,j). Only pairs of distinct actual states in the same fiber will be compared.")),
            Describe.Lean(
                DescribeId.Create("global-partition-car-profile"),
                DeclarationHandle.Create(Prefix + "partitionProfile"),
                H("One global partition law gives a CAR profile"),
                StatementSource.FromAuthor(PartitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any finite type R, choose a partition P(r) of all of K for each r, and a single law p on R with p(r) nonnegative and sum p(r) = 1. Restrict P(r) to A(q) by intersecting each global block with A(q) and discarding empty intersections. The formula gives the weight of each tagged local block. The same P(r) and the same law p are used for every q. Each actual i belongs to exactly one block of each restricted partition, so summing the weights of incident blocks gives sum p(r) = 1. All weights are nonnegative.")),
                    Paragraph(Text("In particular, fix a target t on the actual rows. Take R to be all global partitions whose blocks never contain two states i,j in any common actual fiber A(q) with different targets t(q,i) and t(q,j). A probability law on this finite family gives the public partition profiles to which the antichain theorem applies. Distinct partition laws can have the same profile. The construction only maps global partition laws to CAR profiles; it does not assert that every CAR profile is obtainable from such a law."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tagged-car-pair-antichain"),
                DeclarationHandle.Create(Prefix + "equal_weights_of_common_simulator"),
                H("A common simulator with equal pair masses forces equal weights"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The theorem quantifies over two CAR profiles w and v on the same A and one full stochastic matrix H from O to O: every entry is nonnegative and every input row sums to one. Simulation means W_w H = W_v on every actual row and every output. This single H is independent of the actual state. It can read the source output tag and has no assumed tag or subset support restriction, including on input letters of zero weight.")),
                    Paragraph(Text("Set f(B,C) = w(B) H(B,C). These numbers are nonnegative and have row sums w(B). If B contains an actual i at its tag and C is not incident to that same row, the target row at C is zero. The simulation identity expresses zero as a sum of nonnegative terms containing f(B,C), so f(B,C) = 0. Thus any nonzero flow preserves the tag and satisfies B contained in C. This restriction concerns the weighted flow; it need not restrict H on zero weight input letters.")),
                    Paragraph(Text("Fix q and actual i,j. Expand the target pair mass using the simulated i row, and expand the source pair mass using the flow row sums. The terms for which both i and j already belong to B cancel. What remains is the exact nonnegative pair difference below; here B and C denote underlying subsets at the common tag q.")),
                    new DocumentBlock.DisplayFormula(PairDifferenceFormula()),
                    Paragraph(Text("If B is a proper subset of C and f(B,C) is positive, choose i in B and j in C outside B. They are distinct actual states of the same fiber. Their pair difference contains this positive term. Equal pair masses therefore force every off-diagonal flow to vanish. For each C, its flow row sum then equals f(C,C); an actual i in C and the simulated column identity give f(C,C) = v(C). Hence w(C) = v(C) for every tagged block.")),
                    Paragraph(Text("Consequently, at a fixed array of within-fiber pair masses, two distinct weight profiles admit no simulation in either direction: either direction would force equality. This applies in particular to the profiles constructed from global sufficient partition laws. Singleton fibers require no pair equation, and empty fibers require no row equation. The conclusion distinguishes weight profiles, not their possibly different partition-law representations."))),
                DescribeRole.Theorem))));

    private static Formula Fn(string name, params Formula[] arguments) =>
        Call(name, arguments);

    private static Formula Line(params Formula[] items) => Seq(items);

    private static Formula Gather(params Formula[] lines)
    {
        var items = new List<Formula> { Begin, Grp(F.Id("gathered")) };
        for (var i = 0; i < lines.Length; i++)
        {
            if (i > 0) items.AddRange([RowBreak, Grp()]);
            items.Add(lines[i]);
        }
        items.AddRange([End, Grp(F.Id("gathered"))]);
        return Disp(Seq([.. items]));
    }

    private static Formula TheoremFormula()
    {
        Formula q = F.Id("q"), i = F.Id("i"), j = F.Id("j"), c = F.Id("C");
        Formula w = F.Id("w"), v = F.Id("v"), a = F.Id("A"), h = F.Id("H");
        return Gather(
            Line(Forall, Sp, F.Id("Q"), Comma, F.Id("K"), Colon, F.Id("Type"), Comma,
                Sp, Fn("Fintype", F.Id("Q")), Land, Sp, Fn("Fintype", F.Id("K")), Land, Sp,
                Fn("DecidableEq", F.Id("K")), Comma),
            Line(Forall, Sp, a, Colon, F.Id("Q"), To, Sp, Fn("Finset", F.Id("K")), Comma,
                Sp, w, Comma, v, Colon, Fn("CARProfile", a), Comma),
            Line(Forall, Sp, h, Colon,
                Fn("FiniteMarkovKernel", Fn("TaggedBlock", a), Fn("TaggedBlock", a)), Comma),
            Line(Open, Forall, Sp, F.Id("s"), Colon, Fn("ActualRow", a), Comma,
                Forall, Sp, c, Colon, Fn("TaggedBlock", a), Comma,
                Fn("channelOutput", h, Fn("row", w, F.Id("s")), c), Eq,
                Fn("row", v, F.Id("s"), c), Close, Land),
            Line(Open, Forall, Sp, q, Comma, i, Comma, j, Comma,
                i, InMacro, Sp, Fn("A", q), Land, Sp, j, InMacro, Sp, Fn("A", q), Land, Sp,
                i, Neq, Sp, j, Rightarrow,
                Fn("pairMass", w, q, i, j), Eq, Fn("pairMass", v, q, i, j), Close),
            Line(Rightarrow, Sp, Fn("weight", w), Eq, Fn("weight", v)));
    }

    private static Formula PartitionFormula() => Gather(
        Line(F.Id("R"), Sp, F.Id("finite"), Comma, Sp,
            F.Id("P"), Colon, F.Id("R"), To, Sp, Fn("Partitions", F.Id("K")), Comma,
            Sp, F.Id("p"), Colon, F.Id("R"), To, Sp, Mathbb, Grp(F.Id("R"))),
        Line(Open, Forall, Sp, F.Id("r"), Comma, Num(0), Leq, Sp,
            Fn("p", F.Id("r")), Close, Land, Sp,
            Sum, Underscore, Grp(F.Id("r"), InMacro, Sp, F.Id("R")),
            Fn("p", F.Id("r")), Eq, Num(1)),
        Line(Rightarrow, Sp, F.Id("w"), Eq,
            Fn("partitionProfile", F.Id("A"), F.Id("P"), F.Id("p")),
            Colon, Fn("CARProfile", F.Id("A"))),
        Line(Fn("w", F.Id("q"), F.Id("B")), Eq,
            Sum, Underscore, Grp(F.Id("r"), InMacro, Sp, F.Id("R")),
            Fn("p", F.Id("r")), Cdot, Sp,
            Fn("indicator", Seq(F.Id("B"), InMacro, Sp,
                Fn("restrict", Fn("P", F.Id("r")), Fn("A", F.Id("q")))))));

    private static Formula PairDifferenceFormula() => Disp(Seq(
        Fn("r", F.Id("v"), F.Id("q"), F.Id("i"), F.Id("j")), Minus,
        Fn("r", F.Id("w"), F.Id("q"), F.Id("i"), F.Id("j")), Eq,
        Sum, Underscore, Grp(F.Id("C"), Comma, F.Id("i"), InMacro, Sp, F.Id("C"), Comma,
            F.Id("j"), InMacro, Sp, F.Id("C")),
        Sum, Underscore, Grp(Emptyset, Neq, Sp, F.Id("B"), Subseteq, Sp, F.Id("C"), Comma,
            F.Id("i"), InMacro, Sp, F.Id("B"), Comma, Neg, Open,
            F.Id("j"), InMacro, Sp, F.Id("B"), Close),
        Fn("f", F.Id("B"), F.Id("C")), Geq, Sp, Num(0)));
}
