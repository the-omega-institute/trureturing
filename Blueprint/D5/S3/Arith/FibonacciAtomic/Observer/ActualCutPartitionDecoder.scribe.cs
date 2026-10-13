using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class ActualCutPartitionDecoderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite retained expressions determine common-suffix recuts.",
        H("Finite source-free recutting"),
        Blocks(
            Definition("decoderHoles", "Reached new addresses",
                "Finite navigation of the retained old expression identifies the reached Q addresses and orders them lexicographically."),
            Definition("decoderClass", "Global-label comparison",
                "Each extracted local expression retains the same global old class names. Syntactic equality of these finite expressions determines the first new class ordinal."),
            Definition("recutRow", "Literal exterior recutting",
                "Traverse the old term and replace each reached new cut by its new canonical hole label, copying all remaining constructors and concrete leaves."),
            Definition("rowDecoder", "Total finite decoder",
                "The decoder takes Q and the retained old term only. It neither selects a realizing source nor receives hidden hole values. It is total on raw terms and correct on all realized common-suffix rows."),
            Theorem("common_local_kernel", "Exact local-expression kernel",
                "Under P = Q S, two extracted local terms are equal exactly when their actual Q subtrees are equal, including absent addresses. Forward evaluation uses the same proof valuation. Reverse equality cuts the same actual subtree synchronously by the same suffix S."),
            Theorem("commonSuffix_decoder_correct", "Exact row computation",
                "For every actual source, common-suffix cuts make rowDecoder return its precise canonical Q row, preserving the exterior, reached set, absence guards, and complete partition."),
            Theorem("commonSuffix_recovers", "Sufficient recovery",
                "Equal old rows give equal decoder outputs, hence equal new rows. The decoder supplies the native kernel inclusion."),
            Theorem("commonSuffix_unique", "Unique nonempty suffix",
                "For nonempty prefix-free Q, each q section computes the same S. Prefix ownership and cancellation prove uniqueness."),
            Definition("cutProduct", "Finite cut concatenation",
                "Finite union and image compute all q ++ s for q in Q and s in S."),
            Definition("commonSuffixTest", "Executable finite comparison",
                "Sort Q. If empty, compare P with the empty set. Otherwise take its first q, compute cutSection P q, and compare P with the finite cut product. Every operation has finite decidable equality."),
            Theorem("commonSuffixTest_correct", "Exact decision criterion",
                "For arbitrary finite prefix-free P and Q, the Boolean comparison returns true exactly when a finite prefix-free common suffix exists."),
            Definition("HoleExterior", "Independently addressed exterior",
                "Each hole is named by its native address. Sorting these unique addresses gives the lexicographic hole numbering, while every exterior constructor and concrete Boolean leaf remains literal."),
            Definition("cutExterior", "Literal exterior computation",
                "Stop at public cuts, mark the reached hole by its address, and copy every constructor and concrete leaf outside the cuts. The result contains no hole value."),
            Definition("actualPartition", "Complete finite partition",
                "The finite set contains exactly the pairs of reached holes with equal actual subtrees. Every other reached pair records a genuine disequality."),
            Definition("literalRecord", "Exterior and partition record",
                "This pair computes the addressed exterior and the complete finite partition independently of the class-labelled row representation."),
            Definition("nameExterior", "Address-to-role naming",
                "For any total function names from original addresses to natural numbers, nameExterior is the free-magma lift sending a concrete Boolean leaf to that same literal leaf and an addressed hole p to the role leaf names(p). It preserves every ordered binary pair and every occurrence, including repeated role names. It neither reads a source nor requires names to be injective, and it applies to ground exteriors and a single root hole."),
            Theorem("nameExterior_correct", "Exact structural naming",
                "For arbitrary prefix-free P, root, names, address a and finite subtree t, if names agrees with classOrdinal at every reached ordered P hole and subtree a root is some t, then nameExterior names (cutExterior P a t) equals literalRow P root a t. Both concrete leaves and all reached cut holes are preserved. The statement includes empty and root cuts and arbitrary subtrees of the same root. Together with exteriorHoles_cut and findIdx/idxOf normalization, this structural naming result identifies recordRow of an actual literalRecord with canonicalRow without another structural decoder."),
            Theorem("canonicalRow_record_iff", "Faithful representation bridge",
                "Two sources have the same canonicalRow exactly when their independent exterior and complete partition records agree. The forward direction extracts the exterior and partition. The reverse direction fixes the same reached-hole ordering and first matching indices, then renames the same exterior. Consequently the canonical representation carries exactly the record information, including empty and root holes, without disclosing hidden values, sizes or acquisition traces."),
            Describe.Lean(DescribeId.Create("actualcutpartitiondecoder-exteriorholes-cut"),
                DeclarationHandle.Create(Prefix + "exteriorHoles_cut"), H("Independent exterior hole support"), Statement("exteriorHoles_cut"),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Reading address-marked holes from the actual exterior recovers exactly the reached cuts. This independent support bridge retains original absent cuts and the empty/root cases."))), DescribeRole.Theorem),
            Paragraph(Text("The decoder compares actual retained syntax, not independently renumbered local partitions. Arbitrary substitution injectivity is not used. Absence is determined by visible strict-prefix leaves. The finite decision procedure examines public words only; it does not inspect a source."))
        )));

    private static DocumentBlock Definition(string n, string title, string prose) => Describe.Lean(
        DescribeId.Create("actualcutpartitiondecoder-" + n.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + n), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))),
        DescribeRole.Definition);

    private static DocumentBlock Theorem(string n, string title, string prose) => Describe.Lean(
        DescribeId.Create("actualcutpartitiondecoder-" + n.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + n), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))),
        DescribeRole.Theorem);

    private static StatementSource Statement(string n) => n switch
    {
        "exteriorHoles_cut" => StatementSource.FromAuthor(Disp(All("P", V("CutSet"), All("a", V("Address"), All("t", V("Source"), EqOf(Call("exteriorHoles", V("a"), Call("cutExterior", V("P"), V("a"), V("t"))), Call("reachedHoles", V("P"), V("a"), V("t")))))))),
        _ => StatementSource.WithoutFormula()
    };
    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula All(string ns, Formula t, Formula b) => Seq(Forall, Sp,
        Seq(ns.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()), Colon, Sp, t, Comma, Sp, Par(b));
}
