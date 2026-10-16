using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class ActualCutPartitionRecoveryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Boolean trees retain their complete cut exterior and hole partition.",
        H("Native literal cut rows and actual collision sources"),
        Blocks(
            Definition("CutSet", "Public finite cuts",
                "Cuts are finite List Bool address sets. The empty set and the root address are included."),
            Definition("CutPrefixFree", "Native prefix freedom",
                "Prefix freedom uses the existing IsPrefixFree relation without an additional cut theory."),
            Definition("canonicalRow", "Literal observable term",
                "A FreeMagma (Bool ⊕ Nat) term retains every exterior constructor and concrete Boolean leaf. Each hole carries the first lexicographic reached-hole ordinal in its actual subtree-equality class, rather than its value or size."),
            Theorem("classOrdinal_eq_iff", "Canonical class equality",
                "On reached cuts, equality of first-occurrence ordinals is exactly equality of native subtree options. List.idxOf_inj supplies the first-occurrence fact."),
            Theorem("literalRow_hole_support_aux", "Structural hole support",
                "Extracting addresses from a local literal expression recovers its structural reached-hole support."),
            Theorem("literalRow_hole_support", "Canonical hole support",
                "Hole addresses can be extracted from the observable term itself, including the zero-hole and root-hole cases."),
            Definition("rowAt", "Finite row navigation",
                "Navigation inspects only the retained expression. A concrete or hole leaf prevents any further descent."),
            Definition("holeLabel", "Actual label extraction",
                "The label extractor returns a natural-number class marker only when the navigated term is a hole leaf."),
            Theorem("literalRow_at", "Exterior readout bridge",
                "If no strict ancestor is a cut, navigating the literal expression agrees with native subtree navigation followed by the local cut expression. Thus exterior constructors and Boolean leaves remain readable."),
            Theorem("canonicalRow_at_cut", "Reached cut readout",
                "At a public cut the row contains exactly its class marker when the native subtree exists, and is absent otherwise."),
            Theorem("canonicalRow_reached", "Precise reached support",
                "The holes extracted from canonicalRow are exactly the public cuts intersected with the actual tree positions."),
            Theorem("orderedHoles_mem", "Ordered support",
                "Sorting the extracted support retains exactly the reached public cuts."),
            Theorem("canonicalRow_partition", "Equality and disequality",
                "Equality and disequality of labels actually extracted from the term agree with equality and disequality of all reached native hole values."),
            Theorem("canonicalRow_absent_guard", "Concrete absence guards",
                "Every absent public cut has a strict-prefix Boolean leaf visible in the retained exterior."),
            Theorem("literalRow_evaluate", "Common proof evaluation",
                "A single valuation of the global old labels reconstructs every reached local source. This valuation is used only in proofs; it is not available to a decoder. No injectivity of arbitrary substitution is asserted."),
            Definition("cutSection", "Finite public suffix section",
                "A section filters public cuts with a given prefix and drops that prefix."),
            Theorem("mem_cutSection_iff", "Exact section membership",
                "Section membership is exactly membership of the concatenated address in the original cut."),
            Theorem("cutSection_mem_append", "Section concatenation",
                "A suffix in a section reconstructs a member of the original public cut."),
            Definition("HasCommonSuffix", "Common-suffix equation",
                "A finite prefix-free S witnesses P = {q ++ s : q ∈ Q, s ∈ S}."),
            Theorem("commonSuffix_empty_right", "Empty product",
                "The common-suffix equation with Q empty holds exactly when P is empty."),
            Theorem("commonSuffix_root_right", "Root product",
                "Every prefix-free P is the product of the root cut with P. Recovery follows only after the decoder and kernel classification are supplied."),
            Theorem("cutSection_prefixFree", "Prefix-free sections",
                "Each suffix section of a prefix-free public cut remains prefix-free."),
            Definition("prefixTrie", "Actual finite prefix trie",
                "A depth bounded by the maximum public address length reaches every cut. Unused branches are concrete alpha leaves, and each cut is filled by a native finite source."),
            Describe.Lean(DescribeId.Create("actualcutpartitionrecovery-prefixtrie-at"),
                DeclarationHandle.Create(Prefix + "prefixTrie_at"), H("Actual subtree at a trie cut"), Statement("prefixTrie_at"),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The original trie lemma reaches a ++ r within the supplied depth, provided no strict prefix of r enters the cut. Its unchanged proof is directly consumed by OriginalVector.InterleavedWordRecovery.original_at. Choosing the entire level retains the complete source skeleton, including all unselected leaves."))), DescribeRole.Theorem),
            Theorem("uniform_trie_row", "Uniform old-row collision",
                "Uniformly filling the same trie with any two sources gives the same complete old row: its exterior and its single equality class agree."),
            Theorem("coverage_failure_pair", "Uncovered-hole source pair",
                "Fill every P hole with alpha or every P hole with beta. If one old cut has no Q prefix, its leaf remains visible in the Q exterior, so these actual sources have equal old rows and different new rows."),
            Theorem("idxOf_map_relation", "First matching position under a relation",
                "Two finite mapped value lists have the same first matching position when equality to the target agrees at every list entry. The fact is consumed by class preservation and decoder renaming."),
            Definition("markerContext", "One-class path marker",
                "H_nil a = a; at a false step form mul (H_r a) beta, and at a true step form mul beta (H_r a). Alpha occurs as a complete subtree only at the selected suffix."),
            Definition("Recovers", "Native row kernel inclusion",
                "Recovery means that equal old canonical rows imply equal new canonical rows for every pair of finite nonempty Boolean sources."),
            Theorem("recovery_covers", "Necessary prefix coverage",
                "The actual uncovered-hole collision excludes recovery whenever an old hole lacks a new-cut prefix."),
            Theorem("nonuniform_old_row", "Simultaneous whole-class preservation",
                "Let t = H_s alpha and z = mul t beta. Fill one Q-prefix trie with t; in the other, fill q with H_s z exactly when q ++ s belongs to P. All alpha-valued old holes change together to the fresh z. All other actual values, absent cuts, exterior syntax, and class disequalities remain."),
            Theorem("nonuniform_failure_pair", "Nonuniform source separation",
                "If x ++ s belongs to P and y ++ s does not, the two actual sources have equal complete P rows. Their Q subtrees at x and y were equal and become different. Native subtree leaf-count bounds prove z is fresh, without requiring all P addresses to be reached."),
            Describe.Lean(DescribeId.Create("actualcutpartitionrecovery-classvalue-at"),
                DeclarationHandle.Create(Prefix + "classValue_at"), H("Actual present class value"), Statement("classValue_at"),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("At an originally reached cut, the canonical class valuation equals its actual native subtree. The prefix-free and original-presence premises are retained. The same supplier supports reconstruction and all-class injectivity."))), DescribeRole.Theorem),
            Paragraph(Text("The source domain is every finite nonempty ordered Boolean-leaf tree, and the cuts have no depth or common-shape restriction. The later decoder and classification consume these actual source pairs. This mathematical record makes no physical acquisition or resource-cost assertion."))
        )));

    private static DocumentBlock Definition(string n, string title, string prose) => Describe.Lean(
        DescribeId.Create("actualcutpartitionrecovery-" + n.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + n), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))),
        DescribeRole.Definition);

    private static DocumentBlock Theorem(string n, string title, string prose) => Describe.Lean(
        DescribeId.Create("actualcutpartitionrecovery-" + n.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + n), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))),
        DescribeRole.Theorem);

    private static StatementSource Statement(string n) => n switch
    {
        "prefixTrie_at" => StatementSource.FromAuthor(Disp(All("n", V("Nat"), All("P", V("CutSet"), All("a,r", V("Address"), All("f", Seq(V("Address"), Sp, To, Sp, V("Source")), Imp(And(Mem(Call("append", V("a"), V("r")), V("P")), Seq(Call("length", V("r")), Sp, Leq, Sp, V("n")), All("s", V("Address"), Imp(Call("IsPrefix", V("s"), V("r")), Imp(Seq(V("s"), Sp, Neq, Sp, V("r")), Seq(Neg, Sp, Mem(Call("append", V("a"), V("s")), V("P"))))))), EqOf(Call("subtree", V("r"), Call("prefixTrie", V("n"), V("P"), V("a"), V("f"))), Call("some", Call("f", Call("append", V("a"), V("r")))))))))))),
        "classValue_at" => StatementSource.FromAuthor(Disp(All("P", V("CutSet"), All("u", V("Source"), All("p", V("Address"), All("t", V("Source"), Imp(And(Call("CutPrefixFree", V("P")), Mem(V("p"), V("P")), EqOf(Call("subtree", V("p"), V("u")), Call("some", V("t")))), EqOf(Call("classValue", V("P"), V("u"), Call("classOrdinal", V("P"), V("u"), V("p"))), V("t"))))))))),
        _ => StatementSource.WithoutFormula()
    };
    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(params Formula[] fs) => Seq(fs.Select((f, i) => i == 0 ? Par(f) : Seq(Sp, Land, Sp, Par(f))).ToArray());
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula Mem(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula All(string ns, Formula t, Formula b) => Seq(Forall, Sp,
        Seq(ns.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()), Colon, Sp, t, Comma, Sp, Par(b));
}
