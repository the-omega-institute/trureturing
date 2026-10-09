using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class WordPartitionInverseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/WordPartitionInverse.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Decreasing padded prefix rows, with their endpoint bound, reconstruct one ordered binary word. The full fixed-count, fixed-area joint image is finite and agrees with the image of these actual partitions and of nonempty native trees.",
        H("Word reconstruction and the full joint image"),
        Blocks(
            Node("rows-word", "The guarded inverse word", "wordOfRows_spec", DescribeRole.Theorem, SpecFormula(),
                "Given a decreasing list of natural row lengths bounded by u, build the word by constructing the remaining rows at the first row's endpoint, appending a false letter, then adding the remaining true letters. The resulting word has exactly u true letters and one false letter per row, and its reverse prefix list is exactly the given list. Zero rows and the empty list remain valid."),
            Node("word-rows-word", "Recovering the same word", "wordOfRows_inverse", DescribeRole.Theorem, InverseFormula(),
                "Applying the construction to the actual reverse prefix rows and true count of any word recovers that very word, including the empty auxiliary word and pure-letter words. This recovers the ordered word; it does not recover forgotten tree brackets."),
            Node("zero-padding-word", "Padding rows by zeros", "wordOfRows_padding", DescribeRole.Theorem, PaddingWordFormula(),
                "Appending zero rows corresponds exactly to prepending that many false letters to the reconstructed word. Zero padding does not replace the core word or normalize its area."),
            Paragraph(Text("For every natural row list l and natural padding length m, appending m zeros leaves cellsOfRowLens unchanged: upstream YoungDiagram.mem_cellsOfRowLens describes each cell by an entry bound, and List.getElem_append and List.getElem_replicate make every appended row empty. If l is decreasing, List.pairwise_append and List.pairwise_replicate also give decreasing order after padding; YoungDiagram.mem_ofRowLens and YoungDiagram.ext then identify the same diagram and transpose. The padded carrier retains its declared length. These cell and diagram equalities follow directly from the upstream facts.")),
            Node("outer-reversal", "Exact complete-word reversal", "outer_reverse_contract", DescribeRole.Theorem, ReversalFormula(),
                "Reversing the complete word preserves both counts, complements its scattered pair count within the endpoint rectangle, and preserves both moment coordinates. This is a mathematical comparison of whole words; it grants no reversal operation on an unknown source."),
            Node("partition-fiber", "All guards of the padded partition carrier", "partitionFiber", DescribeRole.Definition, FiberFormula(),
                "The parameters are arbitrary integers. Each carrier list has natural entries, is decreasing, is bounded by the natural part of u, has length v and sum K after casting to the integers, and satisfies all endpoint, nonemptiness and area guards. No area complement or deletion of zero rows is part of this carrier."),
            Node("partition-output", "Both moments of one list", "partitionOutput", DescribeRole.Definition, OutputFormula(),
                "The integer parameters are cast to the reals. squareRows is the sum of the squared real casts of the entries. oddRows weights the entries, starting at index zero, by one, three, five and so on. Both coordinates use the same l."),
            Node("finite-image", "The full nonempty actual joint image", "finite_joint_partition_image", DescribeRole.Theorem, ImageFormula(),
                "For arbitrary integer endpoint and pair-count parameters, take every nonempty binary word with those exact counts. Their distinct joint moment outputs form a finite set, since each word has the fixed length u plus v. This set equals the image of decreasing natural row lists with nonnegative integer parameters u, v and K, positive u plus v, K at most u times v, each row at most u, exactly v entries and sum K. A row list l gives the simultaneous pair (u squared times v - 6uK + 6 squareRows(l), minus u times v squared + 6vK - 6 oddRows(l)). The same set also equals the moment image of native nonempty ordered binary trees. Complete-word reversal identifies this same joint image with the complementary pair count, and its capacity equals the native image cardinality. Negative counts, invalid pair counts and the empty endpoint produce no word source. Each nonempty word has the displayed left-comb representative; recovering an actual tree requires an additional left-comb promise. A representative supplies no physical acquisition, source-membership certification, mutation, calibration or other source authority. No sparse capacity bound or thick-frame family inverse is asserted here.")),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        DescribeRole role, Formula formula, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, Seq(Open, right, Close));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, Seq(Open, right, Close));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Seq(Open, right, Close));
    private static Formula WordType() => Call("List", F.Id("Bool"));
    private static Formula RowType() => Call("List", F.Id("Nat"));
    private static Formula Append(Formula x, Formula y) => Call("append", x, y);
    private static Formula Count(Formula w, string letter) => Call("count", w, F.Id(letter));
    private static Formula Field(Formula x, string name) => Seq(x, Dot, F.Id(name));
    private static Formula IntParameters(Formula body) =>
        All("u", F.Id("Int"), All("v", F.Id("Int"), All("K", F.Id("Int"), body)));
    private static Formula Bound(Formula l, Formula u) =>
        All("x", F.Id("Nat"), Implies(Member(F.Id("x"), l), AtMost(F.Id("x"), u)));

    private static Formula SpecFormula()
    {
        Formula l = F.Id("l"), u = F.Id("u"), w = Call("wordOfRows", u, l);
        return Disp(All("l", RowType(), Implies(Call("SortedGE", l),
            All("u", F.Id("Nat"), Implies(Bound(l, u), And(
                Equal(Count(w, "true"), u), And(Equal(Count(w, "false"), Call("length", l)),
                    Equal(Call("rows", w), l))))))));
    }

    private static Formula InverseFormula()
    {
        Formula w = F.Id("w");
        return Disp(All("w", WordType(), Equal(
            Call("wordOfRows", Count(w, "true"), Call("rows", w)), w)));
    }

    private static Formula PaddingWordFormula()
    {
        Formula u = F.Id("u"), l = F.Id("l"), m = F.Id("m");
        return Disp(All("u", F.Id("Nat"), All("l", RowType(), All("m", F.Id("Nat"), Equal(
            Call("wordOfRows", u, Append(l, Call("replicate", m, D(0)))),
            Append(Call("replicate", m, F.Id("false")), Call("wordOfRows", u, l)))))));
    }

    private static Formula ReversalFormula()
    {
        Formula w = F.Id("w"), r = Call("reverse", w), g = Call("G", w), gr = Call("G", r);
        return Disp(All("w", WordType(), And(Equal(Count(r, "true"), Count(w, "true")), And(
            Equal(Count(r, "false"), Count(w, "false")), And(
            Equal(Call("scatteredTrueFalseCount", r), Seq(Count(w, "true"), Count(w, "false"),
                Minus, Call("scatteredTrueFalseCount", w))), And(
            Equal(Field(gr, "e"), Field(g, "e")), Equal(Field(gr, "f"), Field(g, "f"))))))));
    }

    private static Formula FiberFormula()
    {
        Formula u = F.Id("u"), v = F.Id("v"), k = F.Id("K"), l = F.Id("l");
        Formula guards = And(AtMost(D(0), u), And(AtMost(D(0), v), And(Less(D(0), Seq(u, Plus, v)),
            And(AtMost(D(0), k), And(AtMost(k, Seq(u, v)), And(Call("SortedGE", l),
            And(Bound(l, Call("toNat", u)), And(Equal(Call("integer", Call("length", l)), v),
                Equal(Call("integer", Call("sum", l)), k)))))))));
        return Disp(IntParameters(All("l", RowType(), Iff(
            Member(l, Call("partitionFiber", u, v, k)), guards))));
    }

    private static Formula OutputFormula()
    {
        Formula u = F.Id("u"), v = F.Id("v"), k = F.Id("K"), l = F.Id("l"),
            ur = Call("real", u), vr = Call("real", v), kr = Call("real", k);
        Formula e = Seq(new Formula.Power(ur, D(2)), vr, Minus, D(6), ur, kr,
            Plus, D(6), Call("squareRows", l));
        Formula f = Seq(Minus, ur, new Formula.Power(vr, D(2)), Plus, D(6), vr, kr,
            Minus, D(6), Call("oddRows", l));
        return Disp(IntParameters(All("l", RowType(), Equal(
            Call("partitionOutput", u, v, k, l), Seq(Open, e, Comma, f, Close)))));
    }

    private static Formula ImageFormula()
    {
        Formula u = F.Id("u"), v = F.Id("v"), k = F.Id("K"),
            joint = Call("jointImage", u, v, k), native = Call("nativeImage", u, v, k);
        return Disp(IntParameters(And(Call("Finite", joint), And(Equal(native, joint), And(
            Equal(joint, Call("image", Call("partitionOutput", u, v, k), Call("partitionFiber", u, v, k))),
            And(Equal(joint, Call("jointImage", u, v, Seq(u, v, Minus, k))),
                Equal(Call("capacity", u, v, k), Call("ncard", native))))))));
    }
}
