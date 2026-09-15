using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Partitions;

internal sealed class MixedParityBlockPartitionProductDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/hanna2006a124418");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Parity restriction and gluing prove Hanna's mixed-block partition product.",
        H("Mixed-Parity Blocks in Set Partitions"),
        Blocks(
            Paragraph(Text(
                "An element x of Fin n represents x+1 in the set from 1 through n. "
                + "Thus even zero-based indices represent odd entries, and odd zero-based "
                + "indices represent even entries. Every slash below is natural-number division.")),
            Paragraph(Text(
                "The counting argument restricts each partition to its odd and even entries. "
                + "A mixed block yields one marked block on each side, and the two marked "
                + "families are paired. Gluing paired blocks reverses this restriction.")),
            Node("SetPartition", "Set partitions", SetPartitionFormula(),
                "Set partitions of the universal finite set with r elements.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("stirling2", "Stirling numbers of the second kind", StirlingFormula(),
                "This is the number of partitions of an r-element set into i blocks, the "
                + "Stirling number named in the OEIS formula. The alternating-sum closed form "
                + "for that number is not established here.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("MarkedPartition", "Partitions with marked blocks", MarkedPartitionFormula(),
                "A marked partition consists of a partition and a k-element family of its blocks.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("markedPartitions", "Number of marked partitions", MarkedPartitionsFormula(),
                "The cardinality of the marked-partition family.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("A049020", "The A049020 triangle", A049020Formula(),
                "For each possible block count i, choose k of the i blocks and sum over i.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("markedPartitions_eq_A049020", "Marked partitions realize A049020",
                MarkedA049020Formula(),
                "Decomposition by the number of blocks gives one binomial choice per fiber.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("ParityIndex", "Odd and even index carriers", ParityIndexFormula(),
                "The left summand has the odd entries and the right summand has the even entries.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("ParityBlock", "Parity-split blocks", ParityBlockFormula(),
                "A block is represented by its odd restriction and its even restriction.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("ParityPartition", "Parity-split partitions", ParityPartitionFormula(),
                "These are partitions of the product lattice of odd and even subsets.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("IsMixedBlock", "Mixed parity blocks", IsMixedBlockFormula(),
                "A parity-split block is mixed exactly when both coordinates are nonempty.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("mixedBlockCount", "Number of mixed blocks", MixedBlockCountFormula(),
                "Filter the block family by mixedness and take its cardinality.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("MixedParityPartition", "Partitions with k mixed blocks",
                MixedParityPartitionFormula(),
                "The subtype whose mixed-block count is k.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("T", "The parity-split model", TFormula(),
                "The cardinality of the parity-split partition family with k mixed blocks.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("IsMixedBlockFin", "Literal mixed blocks", IsMixedBlockFinFormula(),
                "For x representing x+1, a block contains witnesses of both entry parities.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Tfin", "The literal set-partition count", TfinFormula(),
                "This directly counts partitions of the set from 1 through n having exactly "
                + "k blocks that contain both odd and even entries.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("T_eq_Tfin", "The model agrees with the literal count", TBridgeFormula(),
                "Splitting Fin n by parity transports partitions bijectively and preserves "
                + "the number of mixed blocks.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("MarkedBlocks", "The marked block family", MarkedBlocksFormula(),
                "Project the selected blocks from a marked partition.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("RestrictionPairingData", "Restriction and pairing data", PairingDataFormula(),
                "The data consists of marked odd and even partitions and a bijection between "
                + "their marked blocks.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("mixedRestrictionEquiv", "Restriction-gluing equivalence",
                RestrictionEquivFormula(),
                "Restriction marks the halves of mixed blocks and pairs them. Gluing paired "
                + "halves and retaining one-sided blocks is its two-sided inverse.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("hanna_a124418", "Hanna's product formula", HannaFormula(),
                "For k at most the integer quotient n/2, restriction produces two marked "
                + "partitions and a bijection of their k marked blocks. The bijection contributes "
                + "k factorial, while the marked families contribute the two A049020 factors.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a124418-mixed-parity-block-partition-product"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a124418-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula SetPartitionFormula() => Def2("SetPartition", "r",
        Call("Finpartition", Call("univ", Call("Fin", V("r")))));
    private static Formula StirlingFormula() => Def3("stirling2", "r", "i",
        Call("card", Subtype("P", Call("SetPartition", V("r")),
            Equal(Call("card", Call("parts", V("P"))), V("i")))));
    private static Formula MarkedPartitionFormula() => Def3("MarkedPartition", "r", "k",
        DependentSum("P", Call("SetPartition", V("r")),
            Subtype("M", Call("Finset", Call("parts", V("P"))),
                Equal(Call("card", V("M")), V("k")))));
    private static Formula MarkedPartitionsFormula() => Def3("markedPartitions", "r", "k",
        Call("card", Call("MarkedPartition", V("r"), V("k"))));
    private static Formula A049020Formula() => Disp(Universal2("r", "k", Equal(
        Call("A049020", V("r"), V("k")), Seq(new Formula.Subscript(Sum,
            Seq(V("i"), Sp, InMacro, Sp, Call("range", Add(V("r"), D(1))))), Sp,
            Multiply(Call("stirling2", V("r"), V("i")),
                Call("choose", V("i"), V("k")))))));
    private static Formula MarkedA049020Formula() => Disp(Universal2("r", "k", Equal(
        Call("markedPartitions", V("r"), V("k")), Call("A049020", V("r"), V("k")))));
    private static Formula ParityIndexFormula() => Def2("ParityIndex", "n", Call("Sum",
        Call("Fin", CeilHalf(V("n"))), Call("Fin", FloorHalf(V("n")))));
    private static Formula ParityBlockFormula() => Def2("ParityBlock", "n", Product(
        Call("Finset", Call("Fin", CeilHalf(V("n")))),
        Call("Finset", Call("Fin", FloorHalf(V("n"))))));
    private static Formula ParityPartitionFormula() => Def2("ParityPartition", "n",
        Call("Finpartition", Pair(Call("univ", Call("Fin", CeilHalf(V("n")))),
            Call("univ", Call("Fin", FloorHalf(V("n")))))));
    private static Formula IsMixedBlockFormula() => Disp(Universal("n", Bound("b",
        Call("ParityBlock", V("n")), Iff(Call("IsMixedBlock", V("b")),
            And(Call("Nonempty", Projection(V("b"), 1)),
                Call("Nonempty", Projection(V("b"), 2)))))));
    private static Formula MixedBlockCountFormula() => Disp(Universal("n", Bound("P",
        Call("ParityPartition", V("n")), Equal(Call("mixedBlockCount", V("P")),
            Call("card", Call("filter", V("IsMixedBlock"),
                Call("parts", V("P"))))))));
    private static Formula MixedParityPartitionFormula() => Def3("MixedParityPartition", "n", "k",
        Subtype("P", Call("ParityPartition", V("n")),
            Equal(Call("mixedBlockCount", V("P")), V("k"))));
    private static Formula TFormula() => Def3("T", "n", "k",
        Call("card", Call("MixedParityPartition", V("n"), V("k"))));
    private static Formula IsMixedBlockFinFormula() => Disp(Universal("n", Bound("b",
        Call("Finset", Call("Fin", V("n"))), Iff(Call("IsMixedBlockFin", V("b")), And(
            ExistsIn("x", V("b"), Call("Odd", Add(Projection(V("x"), "val"), D(1)))),
            ExistsIn("x", V("b"), Call("Even", Add(Projection(V("x"), "val"), D(1)))))))));
    private static Formula TfinFormula() => Def3("Tfin", "n", "k",
        Call("card", Subtype("P", Call("Finpartition", Call("univ", Call("Fin", V("n")))),
            Equal(Call("card", Call("filter", V("IsMixedBlockFin"),
                Call("parts", V("P")))), V("k")))));
    private static Formula TBridgeFormula() => Disp(Universal2("n", "k", Equal(
        Call("T", V("n"), V("k")), Call("Tfin", V("n"), V("k")))));
    private static Formula MarkedBlocksFormula() => Disp(Universal2("r", "k", Bound("P",
        Call("MarkedPartition", V("r"), V("k")), Equal(Call("MarkedBlocks", V("P")),
            Projection(V("P"), 2, 1)))));
    private static Formula PairingDataFormula() => Def3("RestrictionPairingData", "n", "k",
        DependentSum("odd", Call("MarkedPartition", CeilHalf(V("n")), V("k")),
            DependentSum("even", Call("MarkedPartition", FloorHalf(V("n")), V("k")),
                Equivalent(Call("MarkedBlocks", V("odd")),
                    Call("MarkedBlocks", V("even"))))));
    private static Formula RestrictionEquivFormula() => Disp(Universal2("n", "k", Seq(
        Call("MixedParityPartition", V("n"), V("k")), Sp, Equiv, Sp,
        Call("RestrictionPairingData", V("n"), V("k")))));
    private static Formula HannaFormula() => Disp(Universal2("n", "k", ImpliesTo(
        LessOrEqual(V("k"), FloorHalf(V("n"))), Equal(Call("T", V("n"), V("k")),
            Multiply(Multiply(Factorial(V("k")), Call("A049020", FloorHalf(V("n")), V("k"))),
                Call("A049020", CeilHalf(V("n")), V("k")))))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { V(name), Open };
        for (int i = 0; i < arguments.Length; i++)
        {
            if (i > 0) pieces.Add(Comma);
            pieces.Add(arguments[i]);
        }
        pieces.Add(Close);
        return Seq(pieces.ToArray());
    }
    private static Formula Def2(string name, string x, Formula value) =>
        Disp(Universal(x, Equal(Call(name, V(x)), value)));
    private static Formula Def3(string name, string x, string y, Formula value) =>
        Disp(Universal2(x, y, Equal(Call(name, V(x), V(y)), value)));
    private static Formula Universal(string x, Formula body) =>
        Seq(Forall, Sp, V(x), Sp, InMacro, Sp, Naturals(), Comma, Sp, body);
    private static Formula Universal2(string x, string y, Formula body) =>
        Universal(x, Universal(y, body));
    private static Formula Bound(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsIn(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Naturals() => V("N");
    private static Formula Subtype(string name, Formula type, Formula predicate) =>
        Seq(OpenBrace, V(name), Sp, Colon, Sp, type, Sp, Mid, Sp, predicate, CloseBrace);
    private static Formula DependentSum(string name, Formula type, Formula body) =>
        Seq(Sigma, Sp, V(name), Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Pair(Formula left, Formula right) =>
        Parenthesized(Seq(left, Comma, Sp, right));
    private static Formula Product(Formula left, Formula right) =>
        Seq(left, Sp, Times, Sp, right);
    private static Formula Projection(Formula value, params int[] fields)
    {
        var pieces = new List<Formula> { value };
        foreach (var field in fields)
        {
            pieces.Add(Dot);
            pieces.Add(D((byte)field));
        }
        return Seq(pieces.ToArray());
    }
    private static Formula Projection(Formula value, string field) =>
        Seq(value, Dot, V(field));
    private static Formula FloorHalf(Formula n) =>
        Seq(Lfloor, Sp, n, Sp, Slash, Sp, D(2), Rfloor);
    private static Formula CeilHalf(Formula n) =>
        Seq(Lfloor, Parenthesized(Add(n, D(1))), Sp, Slash, Sp, D(2), Rfloor);
    private static Formula Equal(Formula left, Formula right) =>
        Seq(left, Sp, Eq, Sp, right);
    private static Formula Equivalent(Formula left, Formula right) =>
        Seq(left, Sp, Equiv, Sp, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff,
            Parenthesized(right));
    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula ImpliesTo(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Factorial(Formula value) => Seq(value, Bang);
}
