using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.BridgeGraph;

internal sealed class FloorSelectorCyclesDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles";
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Qualified(string owner, string name) =>
        Qualified(F.Id(owner), Dot, F.Id(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula Qualified(params Formula[] names) => Seq(Operatorname, Grp(names));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "FloorSelectorCycles supplies the width-three bridge max-flow proof.",
        H("FloorSelectorCycles"), Blocks(
            Paragraph(Text("Formulas retain the Lean parameter types and all hypotheses. HDiv.hDiv and HMod.hMod are displayed infix: on natural and integer carriers they mean the respective Lean integer division and remainder operations; on rational carriers division is field division. Coe.coe denotes the coercion determined by the displayed target type. Finite and dependent-pair constructors omit proof fields, which do not change their values. A dash in a match pattern is an anonymous wildcard. CoeFun.coe and CoeSort.coe retain coercions to functions and types. All dimensions use ℕ, all construction coefficients use ℚ, and max-flow uses ℂ.")),
            Describe.Lean(DescribeId.Create("gls-floorselectorcycles-jump"),
                DeclarationHandle.Create(Owner + ".jump"),
                H("jump"), StatementSource.FromAuthor(Disp(Statement0())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The defining expression fixes jump for the consumed FloorSelectorCycles construction."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gls-floorselectorcycles-jump-zero-or-one"),
                DeclarationHandle.Create(Owner + ".jump_zero_or_one"),
                H("jump_zero_or_one"), StatementSource.FromAuthor(Disp(Statement1())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("jump_zero_or_one is used on the live proof path of the width-three bridge construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-floorselectorcycles-opposite-direction-excess"),
                DeclarationHandle.Create(Owner + ".opposite_direction_excess"),
                H("opposite_direction_excess"), StatementSource.FromAuthor(Disp(Statement2())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("opposite_direction_excess is used on the live proof path of the width-three bridge construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-floorselectorcycles-jump-one-iff-fin-selector"),
                DeclarationHandle.Create(Owner + ".jump_one_iff_fin_selector"),
                H("jump_one_iff_fin_selector"), StatementSource.FromAuthor(Disp(Statement3())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("jump_one_iff_fin_selector is used on the live proof path of the width-three bridge construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-floorselectorcycles-monodromy-forces-zero"),
                DeclarationHandle.Create(Owner + ".monodromy_forces_zero"),
                H("monodromy_forces_zero"), StatementSource.FromAuthor(Disp(Statement4())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("monodromy_forces_zero is used on the live proof path of the width-three bridge construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-floorselectorcycles-half-pow-lt-one"),
                DeclarationHandle.Create(Owner + ".half_pow_lt_one"),
                H("half_pow_lt_one"), StatementSource.FromAuthor(Disp(Statement5())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("half_pow_lt_one is used on the live proof path of the width-three bridge construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-floorselectorcycles-recurrence-product-bounded"),
                DeclarationHandle.Create(Owner + ".recurrence_product_bounded"),
                H("recurrence_product_bounded"), StatementSource.FromAuthor(Disp(Statement6())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("recurrence_product_bounded is used on the live proof path of the width-three bridge construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-floorselectorcycles-balanced-cycle-zero"),
                DeclarationHandle.Create(Owner + ".balanced_cycle_zero"),
                H("balanced_cycle_zero"), StatementSource.FromAuthor(Disp(Statement7())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A balanced interval count excludes two unmatched input events. Propagation around a positive-period cycle then yields a multiplicative monodromy strictly below one, forcing every coordinate to vanish."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-floorselectorcycles-common-node-product-bound"),
                DeclarationHandle.Create(Owner + ".common_node_product_bound"),
                H("common_node_product_bound"), StatementSource.FromAuthor(Disp(Statement8())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("common_node_product_bound is used on the live proof path of the width-three bridge construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-floorselectorcycles-backward"),
                DeclarationHandle.Create(Owner + ".backward"),
                H("backward"), StatementSource.FromAuthor(Disp(Statement9())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The defining expression fixes backward for the consumed FloorSelectorCycles construction."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gls-floorselectorcycles-backward-apply"),
                DeclarationHandle.Create(Owner + ".backward_apply"),
                H("backward_apply"), StatementSource.FromAuthor(Disp(Statement10())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("backward_apply is used on the live proof path of the width-three bridge construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-floorselectorcycles-forwardhalf"),
                DeclarationHandle.Create(Owner + ".forwardHalf"),
                H("forwardHalf"), StatementSource.FromAuthor(Disp(Statement11())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The defining expression fixes forwardHalf for the consumed FloorSelectorCycles construction."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gls-floorselectorcycles-forwardhalf-apply"),
                DeclarationHandle.Create(Owner + ".forwardHalf_apply"),
                H("forwardHalf_apply"), StatementSource.FromAuthor(Disp(Statement12())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("forwardHalf_apply is used on the live proof path of the width-three bridge construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-floorselectorcycles-rowselector"),
                DeclarationHandle.Create(Owner + ".rowSelector"),
                H("rowSelector"), StatementSource.FromAuthor(Disp(Statement13())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The defining expression fixes rowSelector for the consumed FloorSelectorCycles construction."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gls-floorselectorcycles-reservoir"),
                DeclarationHandle.Create(Owner + ".reservoir"),
                H("reservoir"), StatementSource.FromAuthor(Disp(Statement14())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The defining expression fixes reservoir for the consumed FloorSelectorCycles construction."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gls-floorselectorcycles-schurmap"),
                DeclarationHandle.Create(Owner + ".schurMap"),
                H("schurMap"), StatementSource.FromAuthor(Disp(Statement15())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The defining expression fixes schurMap for the consumed FloorSelectorCycles construction."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gls-floorselectorcycles-cyclicresolventlemma"),
                DeclarationHandle.Create(Owner + ".CyclicResolventLemma"),
                H("CyclicResolventLemma"), StatementSource.FromAuthor(Disp(Statement16())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The defining expression fixes CyclicResolventLemma for the consumed FloorSelectorCycles construction."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gls-floorselectorcycles-index"),
                DeclarationHandle.Create(Owner + ".index"),
                H("index"), StatementSource.FromAuthor(Disp(Statement17())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The defining expression fixes index for the consumed FloorSelectorCycles construction."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gls-floorselectorcycles-index-val-int"),
                DeclarationHandle.Create(Owner + ".index_val_int"),
                H("index_val_int"), StatementSource.FromAuthor(Disp(Statement18())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("index_val_int is used on the live proof path of the width-three bridge construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-floorselectorcycles-index-nat"),
                DeclarationHandle.Create(Owner + ".index_nat"),
                H("index_nat"), StatementSource.FromAuthor(Disp(Statement19())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("index_nat is used on the live proof path of the width-three bridge construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-floorselectorcycles-index-add-multiple"),
                DeclarationHandle.Create(Owner + ".index_add_multiple"),
                H("index_add_multiple"), StatementSource.FromAuthor(Disp(Statement20())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("index_add_multiple is used on the live proof path of the width-three bridge construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-floorselectorcycles-index-add-one"),
                DeclarationHandle.Create(Owner + ".index_add_one"),
                H("index_add_one"), StatementSource.FromAuthor(Disp(Statement21())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("index_add_one is used on the live proof path of the width-three bridge construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-floorselectorcycles-index-sub-one"),
                DeclarationHandle.Create(Owner + ".index_sub_one"),
                H("index_sub_one"), StatementSource.FromAuthor(Disp(Statement22())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("index_sub_one is used on the live proof path of the width-three bridge construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-floorselectorcycles-orbit"),
                DeclarationHandle.Create(Owner + ".orbit"),
                H("orbit"), StatementSource.FromAuthor(Disp(Statement23())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The defining expression fixes orbit for the consumed FloorSelectorCycles construction."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gls-floorselectorcycles-edge"),
                DeclarationHandle.Create(Owner + ".edge"),
                H("edge"), StatementSource.FromAuthor(Disp(Statement24())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The defining expression fixes edge for the consumed FloorSelectorCycles construction."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gls-floorselectorcycles-orbit-period"),
                DeclarationHandle.Create(Owner + ".orbit_period"),
                H("orbit_period"), StatementSource.FromAuthor(Disp(Statement25())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("orbit_period is used on the live proof path of the width-three bridge construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-floorselectorcycles-edge-pos"),
                DeclarationHandle.Create(Owner + ".edge_pos"),
                H("edge_pos"), StatementSource.FromAuthor(Disp(Statement26())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("edge_pos is used on the live proof path of the width-three bridge construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-floorselectorcycles-tensor-mulvec-orbit"),
                DeclarationHandle.Create(Owner + ".tensor_mulVec_orbit"),
                H("tensor_mulVec_orbit"), StatementSource.FromAuthor(Disp(Statement27())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("tensor_mulVec_orbit is used on the live proof path of the width-three bridge construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-floorselectorcycles-whole-tensor-excess"),
                DeclarationHandle.Create(Owner + ".whole_tensor_excess"),
                H("whole_tensor_excess"), StatementSource.FromAuthor(Disp(Statement28())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("whole_tensor_excess is used on the live proof path of the width-three bridge construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-floorselectorcycles-jump-index"),
                DeclarationHandle.Create(Owner + ".jump_index"),
                H("jump_index"), StatementSource.FromAuthor(Disp(Statement29())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("jump_index is used on the live proof path of the width-three bridge construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-floorselectorcycles-edge-product"),
                DeclarationHandle.Create(Owner + ".edge_product"),
                H("edge_product"), StatementSource.FromAuthor(Disp(Statement30())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("edge_product is used on the live proof path of the width-three bridge construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-floorselectorcycles-tensor-edge-product-lt-one"),
                DeclarationHandle.Create(Owner + ".tensor_edge_product_lt_one"),
                H("tensor_edge_product_lt_one"), StatementSource.FromAuthor(Disp(Statement31())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("tensor_edge_product_lt_one is used on the live proof path of the width-three bridge construction."))),
                DescribeRole.Theorem))));

    private static Formula Statement0() =>
        Seq(Forall, Sp, Parenthesized(Seq(Rho, Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp,
        Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Comma, Sp,
        Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("jump")), Sp, Rho, Sp, F.Id("n"), Sp, Eq, Sp,
        Parenthesized(Seq(new Formula.Apply(Qualified("Int", "ceil"), [Seq(Parenthesized(new
        Formula.Apply(Qualified("Coe", "coe"), [Seq(F.Id("n"), Sp, Plus, Sp, D(1))])), Sp, Cdot, Sp, Rho)]), Sp,
        Minus, Sp, new Formula.Apply(Qualified("Int", "ceil"), [Seq(Parenthesized(new Formula.Apply(Qualified("Coe",
        "coe"), [F.Id("n")])), Sp, Cdot, Sp, Rho)]))));

    private static Formula Statement1() =>
        Seq(Forall, Sp, Seq(OpenBrace, Seq(Rho, Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Q")))), CloseBrace), Sp, Comma,
        Sp, D(0), Sp, Leq, Sp, Rho, Sp, To, Sp, Rho, Sp, Leq, Sp, D(1), Sp, To, Sp, Forall, Sp,
        Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Comma, Sp,
        Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("jump")), Sp, Rho, Sp, F.Id("n"), Sp, Eq, Sp, D(0), Sp, Lor,
        Sp, Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("jump")), Sp, Rho, Sp, F.Id("n"), Sp, Eq, Sp, D(1));

    private static Formula Statement2() =>
        Seq(Forall, Sp, Seq(OpenBrace, Seq(new Formula.Subscript(Rho, F.Id("I")), Sp, new Formula.Subscript(Rho,
        F.Id("O")), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Q")))), CloseBrace), Sp, Comma, Sp, new
        Formula.Subscript(Rho, F.Id("I")), Sp, Leq, Sp, new Formula.Subscript(Rho, F.Id("O")), Sp, To, Sp, Forall, Sp,
        Parenthesized(Seq(F.Id("phaseI"), Sp, F.Id("phaseO"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp,
        Parenthesized(Seq(F.Id("len"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Seq(new
        Formula.Subscript(Sum, Seq(F.Id("t"), Sp, InMacro, Sp, Qualified(F.Id("Finset"), Dot, F.Id("range")), Sp,
        F.Id("len"))), Sp, Parenthesized(Parenthesized(Seq(Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("jump")),
        Sp, new Formula.Subscript(Rho, F.Id("I")), Sp, Parenthesized(Seq(F.Id("phaseI"), Sp, Plus, Sp,
        Parenthesized(new Formula.Apply(Qualified("Coe", "coe"), [F.Id("t")])))), Sp, Minus, Sp,
        Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("jump")), Sp, new Formula.Subscript(Rho, F.Id("O")), Sp,
        Parenthesized(Seq(F.Id("phaseO"), Sp, Minus, Sp, Parenthesized(new Formula.Apply(Qualified("Coe", "coe"),
        [F.Id("t")])))))))), Sp, Leq, Sp, D(1));

    private static Formula Statement3() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("B"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp,
        Comma, Sp, D(0), Sp, F.Lt, Sp, F.Id("B"), Sp, To, Sp, F.Id("B"), Sp, Leq, Sp, F.Id("A"), Sp, To, Sp, Forall,
        Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("A"))), Sp, Comma, Sp,
        Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("jump")), Sp, Parenthesized(Seq(Parenthesized(Parenthesized(Seq(F.Id("B"), Colon, Seq(Mathbb, Grp(F.Id("Q")))))), Sp, Qualified("HDiv", "hDiv"), Sp, Parenthesized(Parenthesized(Seq(F.Id("A"), Colon, Seq(Mathbb, Grp(F.Id("Q")))))))), Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Call("val", F.Id("n"))), Colon, Seq(Mathbb, Grp(F.Id("Z")))))), Sp, Eq, Sp, D(1), Sp, Iff,
        Sp, Exists, Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("B"))), Sp, Comma, Sp,
        Parenthesized(Call("val", F.Id("n"))), Sp, Eq, Sp, Parenthesized(Call("val", F.Id("k"))), Sp, Cdot, Sp, F.Id("A"), Sp, Qualified("HDiv", "hDiv"),
        Sp, F.Id("B"));

    private static Formula Statement4() =>
        Seq(Forall, Sp, Parenthesized(Seq(Mu, Sp, F.Id("z"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Comma,
        Sp, Mu, Sp, F.Lt, Sp, D(1), Sp, To, Sp, F.Id("z"), Sp, Eq, Sp, Mu, Sp, Cdot, Sp, F.Id("z"), Sp, To, Sp,
        F.Id("z"), Sp, Eq, Sp, D(0));

    private static Formula Statement5() =>
        Seq(Forall, Sp, Seq(OpenBrace, Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), CloseBrace), Sp,
        Comma, Sp, D(0), Sp, F.Lt, Sp, F.Id("n"), Sp, To, Sp, new Formula.Power(Parenthesized(Seq(D(1), Sp,
        Qualified("HDiv", "hDiv"), Sp, D(2))), F.Id("n")), Sp, F.Lt, Sp, D(1));

    private static Formula Statement6() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("z"), Sp, F.Id("f"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp,
        To, Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Seq(Mathbb,
        Grp(F.Id("N"))))), Sp, Comma, Sp, Parenthesized(Seq(Forall, Sp, F.Id("n"), Sp, F.Lt, Sp, F.Id("L"), Sp, Comma,
        Sp, F.Id("z"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(1))), Sp, Eq, Sp, F.Id("f"), Sp, F.Id("n"),
        Sp, Cdot, Sp, F.Id("z"), Sp, F.Id("n"))), Sp, To, Sp, F.Id("z"), Sp, F.Id("L"), Sp, Eq, Sp,
        Parenthesized(Seq(new Formula.Subscript(Prod, Seq(F.Id("t"), Sp, InMacro, Sp, Qualified(F.Id("Finset"), Dot,
        F.Id("range")), Sp, F.Id("L"))), Sp, Parenthesized(Seq(F.Id("f"), Sp, F.Id("t"))))), Sp, Cdot, Sp, F.Id("z"),
        Sp, D(0));

    private static Formula Statement7() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("i"), Sp, F.Id("o"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))), Sp,
        To, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Parenthesized(Seq(F.Id("z"), Sp, F.Id("c"), Sp, Colon, Sp,
        Seq(Mathbb, Grp(F.Id("Z"))), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Comma, Sp,
        Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp,
        Comma, Sp, F.Id("i"), Sp, F.Id("n"), Sp, Eq, Sp, D(0), Sp, Lor, Sp, F.Id("i"), Sp, F.Id("n"), Sp, Eq, Sp,
        D(1))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb,
        Grp(F.Id("Z"))))), Sp, Comma, Sp, F.Id("o"), Sp, F.Id("n"), Sp, Eq, Sp, D(0), Sp, Lor, Sp, F.Id("o"), Sp,
        F.Id("n"), Sp, Eq, Sp, D(1))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp,
        Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Comma, Sp, F.Id("i"), Sp, F.Id("n"), Sp, Eq, Sp, F.Id("o"), Sp,
        F.Id("n"), Sp, To, Sp, F.Id("z"), Sp, F.Id("n"), Sp, Eq, Sp, F.Id("c"), Sp, F.Id("n"), Sp, Cdot, Sp,
        F.Id("z"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Minus, Sp, D(1))))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp,
        Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Comma, Sp, F.Id("c"), Sp,
        F.Id("n"), Sp, Neq, Sp, D(0))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp,
        Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Comma, Sp, F.Id("i"), Sp, F.Id("n"), Sp, Eq, Sp, D(0), Sp, To,
        Sp, F.Id("o"), Sp, F.Id("n"), Sp, Eq, Sp, D(1), Sp, To, Sp, F.Id("z"), Sp, F.Id("n"), Sp, Eq, Sp, D(0), Sp,
        Land, Sp, F.Id("z"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Minus, Sp, D(1))), Sp, Eq, Sp, D(0))), Sp, To, Sp,
        Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp,
        Parenthesized(Seq(F.Id("len"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Seq(new
        Formula.Subscript(Sum, Seq(F.Id("t"), Sp, InMacro, Sp, Qualified(F.Id("Finset"), Dot, F.Id("range")), Sp,
        F.Id("len"))), Sp, Parenthesized(Parenthesized(Seq(F.Id("i"), Sp, Parenthesized(Seq(F.Id("a"), Sp, Plus, Sp,
        Parenthesized(new Formula.Apply(Qualified("Coe", "coe"), [F.Id("t")])))), Sp, Minus, Sp, F.Id("o"), Sp,
        Parenthesized(Seq(F.Id("a"), Sp, Plus, Sp, Parenthesized(new Formula.Apply(Qualified("Coe", "coe"),
        [F.Id("t")])))))))), Sp, Leq, Sp, D(1))), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp,
        Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, D(0), Sp, F.Lt, Sp, F.Id("L"), Sp, To, Sp,
        Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp,
        Comma, Sp, F.Id("z"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, Parenthesized(new
        Formula.Apply(Qualified("Coe", "coe"), [F.Id("L")])))), Sp, Eq, Sp, F.Id("z"), Sp, F.Id("n"))), Sp, To, Sp,
        Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp,
        Comma, Sp, Seq(new Formula.Subscript(Sum, Seq(F.Id("t"), Sp, InMacro, Sp, Qualified(F.Id("Finset"), Dot,
        F.Id("range")), Sp, F.Id("L"))), Sp, Parenthesized(Parenthesized(Seq(F.Id("i"), Sp,
        Parenthesized(Seq(F.Id("a"), Sp, Plus, Sp, Parenthesized(new Formula.Apply(Qualified("Coe", "coe"),
        [F.Id("t")])))), Sp, Minus, Sp, F.Id("o"), Sp, Parenthesized(Seq(F.Id("a"), Sp, Plus, Sp, Parenthesized(new
        Formula.Apply(Qualified("Coe", "coe"), [F.Id("t")])))))))), Sp, Leq, Sp, D(0))), Sp, To, Sp,
        Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp,
        Comma, Sp, Seq(new Formula.Subscript(Prod, Seq(F.Id("t"), Sp, InMacro, Sp, Qualified(F.Id("Finset"), Dot,
        F.Id("range")), Sp, F.Id("L"))), Sp, Parenthesized(Seq(F.Id("c"), Sp, Parenthesized(Seq(F.Id("a"), Sp, Plus,
        Sp, Parenthesized(new Formula.Apply(Qualified("Coe", "coe"), [F.Id("t")])), Sp, Plus, Sp, D(1)))))), Sp, F.Lt,
        Sp, D(1))), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))),
        Sp, Comma, Sp, F.Id("z"), Sp, F.Id("a"), Sp, Eq, Sp, D(0));

    private static Formula Statement8() =>
        Seq(Forall, Sp, Parenthesized(Seq(Kappa, Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Comma, Sp, D(0),
        Sp, F.Lt, Sp, Kappa, Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("o"), Sp, Colon, Sp, Seq(Mathbb,
        Grp(F.Id("Z"))), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Parenthesized(Seq(F.Id("w"), Sp, Colon, Sp,
        Seq(Mathbb, Grp(F.Id("Z"))), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Comma, Sp,
        Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp,
        Comma, Sp, D(0), Sp, F.Lt, Sp, F.Id("w"), Sp, F.Id("n"))), Sp, To, Sp, Forall, Sp,
        Parenthesized(Seq(F.Id("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Parenthesized(Seq(F.Id("L"),
        Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Seq(new Formula.Subscript(Prod, Seq(F.Id("t"),
        Sp, InMacro, Sp, Qualified(F.Id("Finset"), Dot, F.Id("range")), Sp, F.Id("L"))), Sp,
        Parenthesized(Seq(Parenthesized(Seq(F.Id("if"), Sp, F.Id("o"), Sp, Parenthesized(Seq(F.Id("a"), Sp, Plus, Sp,
        Parenthesized(new Formula.Apply(Qualified("Coe", "coe"), [F.Id("t")])), Sp, Plus, Sp, D(1))), Sp, Eq, Sp,
        D(1), Sp, F.Id("then"), Sp, Kappa, Sp, Qualified("HDiv", "hDiv"), Sp, Parenthesized(Seq(Kappa, Sp, Plus, Sp,
        D(1))), Sp, F.Id("else"), Sp, D(1))), Sp, Cdot, Sp, F.Id("w"), Sp, Parenthesized(Seq(F.Id("a"), Sp, Plus, Sp,
        Parenthesized(new Formula.Apply(Qualified("Coe", "coe"), [F.Id("t")])), Sp, Plus, Sp, D(1)))))), Sp, Leq, Sp,
        Seq(new Formula.Subscript(Prod, Seq(F.Id("t"), Sp, InMacro, Sp, Qualified(F.Id("Finset"), Dot, F.Id("range")),
        Sp, F.Id("L"))), Sp, Parenthesized(Seq(F.Id("w"), Sp, Parenthesized(Seq(F.Id("a"), Sp, Plus, Sp,
        Parenthesized(new Formula.Apply(Qualified("Coe", "coe"), [F.Id("t")])), Sp, Plus, Sp, D(1)))))));

    private static Formula Statement9() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp,
        Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("backward")), Sp, F.Id("A"), Sp, Eq, Sp,
        Parenthesized(Seq(Qualified(F.Id("Matrix"), Dot, F.Id("submatrix")), Sp, D(1), Sp,
        Parenthesized(Parenthesized(new Formula.Apply(Qualified("CoeFun", "coe"), [Seq(F.Id("finRotate"), Sp,
        F.Id("A"))]))), Sp, F.Id("id"))));

    private static Formula Statement10() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp,
        Parenthesized(Seq(F.Id("i"), Sp, F.Id("j"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("A"))), Sp, Comma, Sp,
        Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("backward")), Sp, F.Id("A"), Sp, F.Id("i"), Sp, F.Id("j"),
        Sp, Eq, Sp, F.Id("if"), Sp, Parenthesized(Call("val", F.Id("j"))), Sp, Eq,
        Sp, Parenthesized(Seq(Parenthesized(Call("val", F.Id("i"))), Sp, Plus, Sp,
        D(1))), Sp, Qualified("HMod", "hMod"), Sp, F.Id("A"), Sp, F.Id("then"), Sp, D(1), Sp, F.Id("else"), Sp, D(0));

    private static Formula Statement11() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("G"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp,
        Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("forwardHalf")), Sp, F.Id("G"), Sp, Eq, Sp,
        Parenthesized(Seq(Parenthesized(Seq(Qualified(F.Id("Matrix"), Dot, F.Id("diagonal")), Sp, F.Id("fun"), Sp,
        Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("G"))), Sp, Mapsto, Sp, F.Id("if"), Sp,
        Parenthesized(Call("val", F.Id("k"))), Sp, Eq, Sp, D(0), Sp, F.Id("then"),
        Sp, D(1), Sp, Qualified("HDiv", "hDiv"), Sp, D(2), Sp, F.Id("else"), Sp, D(1))), Sp, Dot, Sp,
        F.Id("submatrix"), Sp, F.Id("id"), Sp, Parenthesized(new Formula.Apply(Qualified("CoeFun", "coe"),
        [Seq(F.Id("finRotate"), Sp, F.Id("G"))])))));

    private static Formula Statement12() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("G"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp,
        Parenthesized(Seq(F.Id("i"), Sp, F.Id("j"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("G"))), Sp, Comma, Sp,
        Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("forwardHalf")), Sp, F.Id("G"), Sp, F.Id("i"), Sp, F.Id("j"),
        Sp, Eq, Sp, F.Id("if"), Sp, Parenthesized(Call("val", F.Id("j"))), Sp, Eq,
        Sp, Parenthesized(Seq(Parenthesized(Call("val", F.Id("i"))), Sp, Plus, Sp,
        F.Id("G"), Sp, Minus, Sp, D(1))), Sp, Qualified("HMod", "hMod"), Sp, F.Id("G"), Sp, F.Id("then"), Sp,
        F.Id("if"), Sp, Parenthesized(Call("val", F.Id("i"))), Sp, Eq, Sp, D(0), Sp,
        F.Id("then"), Sp, D(1), Sp, Qualified("HDiv", "hDiv"), Sp, D(2), Sp, F.Id("else"), Sp, D(1), Sp, F.Id("else"),
        Sp, D(0));

    private static Formula Statement13() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("B"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp,
        Comma, Sp, Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("rowSelector")), Sp, F.Id("A"), Sp, F.Id("B"), Sp,
        Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(Qualified(F.Id("Matrix"), Dot, F.Id("submatrix")), Sp, D(1), Sp,
        Qualified(F.Id("Fin"), Dot, F.Id("val")), Sp, F.Id("fun"), Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp,
        F.Id("Fin"), Sp, F.Id("B"))), Sp, Mapsto, Sp, Parenthesized(Call("val", F.Id("k"))), Sp, Cdot, Sp, F.Id("A"), Sp, Qualified("HDiv", "hDiv"), Sp, F.Id("B"))), Sp, Dot, Sp,
        F.Id("transpose"))));

    private static Formula Statement14() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("G"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp,
        Comma, Sp, Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("reservoir")), Sp, F.Id("A"), Sp, F.Id("G"), Sp,
        Eq, Sp, Parenthesized(Seq(D(1), Sp, Plus, Sp, Parenthesized(Seq(Minus, Sp,
        Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("backward")), Sp, F.Id("A"))), Sp, Dot, Sp,
        F.Id("kronecker"), Sp, Parenthesized(Seq(Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("forwardHalf")), Sp,
        F.Id("G"))))));

    private static Formula Statement15() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("B"), Sp, F.Id("G"), Sp, F.Id("D"), Sp, Colon, Sp,
        Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(Kappa, Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp,
        Comma, Sp, Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("schurMap")), Sp, F.Id("A"), Sp, F.Id("B"), Sp,
        F.Id("G"), Sp, F.Id("D"), Sp, Kappa, Sp, Eq, Sp, Parenthesized(Seq(Kappa, Sp, Cdot, Sp,
        Parenthesized(Seq(Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("rowSelector")), Sp, F.Id("A"), Sp,
        F.Id("B"))), Sp, Dot, Sp, F.Id("kronecker"), Sp, Parenthesized(Seq(Qualified(F.Id("FloorSelectorCycles"), Dot,
        F.Id("rowSelector")), Sp, F.Id("G"), Sp, F.Id("D"))), Sp, Dot, Sp, F.Id("transpose"), Sp, Plus, Sp,
        Parenthesized(Seq(Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("rowSelector")), Sp, F.Id("A"), Sp,
        F.Id("B"))), Sp, Dot, Sp, F.Id("kronecker"), Sp, D(1), Sp, Cdot, Sp, new
        Formula.Power(Parenthesized(Seq(Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("reservoir")), Sp, F.Id("A"),
        Sp, F.Id("G"))), new Formula.Negate(D(1))), Sp, Cdot, Sp, Qualified(F.Id("Matrix"), Dot, F.Id("kronecker")),
        Sp, D(1), Sp, Parenthesized(Seq(Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("rowSelector")), Sp,
        F.Id("G"), Sp, F.Id("D"))), Sp, Dot, Sp, F.Id("transpose"))));

    private static Formula Statement16() =>
        Seq(Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("CyclicResolventLemma")), Sp, Iff, Sp,
        Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("B"), Sp, F.Id("G"), Sp, F.Id("D"), Sp,
        Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, D(0), Sp, F.Lt, Sp, F.Id("B"), Sp, To, Sp, F.Id("B"),
        Sp, Leq, Sp, F.Id("A"), Sp, To, Sp, D(0), Sp, F.Lt, Sp, F.Id("D"), Sp, To, Sp, F.Id("D"), Sp, Leq, Sp,
        F.Id("G"), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(Kappa, Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp,
        Comma, Sp, D(0), Sp, F.Lt, Sp, Kappa, Sp, To, Sp, F.Id("IsUnit"), Sp,
        Parenthesized(Seq(Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("reservoir")), Sp, F.Id("A"), Sp,
        F.Id("G"))), Sp, Land, Sp, Parenthesized(Seq(F.Id("A"), Sp, Cdot, Sp, F.Id("D"), Sp, Leq, Sp, F.Id("B"), Sp,
        Cdot, Sp, F.Id("G"), Sp, To, Sp, Qualified(F.Id("Function"), Dot, F.Id("Injective")), Sp,
        Parenthesized(Seq(Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("schurMap")), Sp, F.Id("A"), Sp, F.Id("B"),
        Sp, F.Id("G"), Sp, F.Id("D"), Sp, Kappa)), Sp, Dot, Sp, F.Id("mulVec"))), Sp, Land, Sp,
        Parenthesized(Seq(F.Id("B"), Sp, Cdot, Sp, F.Id("G"), Sp, Leq, Sp, F.Id("A"), Sp, Cdot, Sp, F.Id("D"), Sp, To,
        Sp, Qualified(F.Id("Function"), Dot, F.Id("Surjective")), Sp,
        Parenthesized(Seq(Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("schurMap")), Sp, F.Id("A"), Sp, F.Id("B"),
        Sp, F.Id("G"), Sp, F.Id("D"), Sp, Kappa)), Sp, Dot, Sp, F.Id("mulVec"))))));

    private static Formula Statement17() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("N"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp,
        Parenthesized(Seq(F.Id("hN"), Sp, Colon, Sp, D(0), Sp, F.Lt, Sp, F.Id("N"))), Sp, Parenthesized(Seq(F.Id("s"),
        Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Comma, Sp, Qualified(F.Id("FloorSelectorCycles"), Dot,
        F.Id("index")), Sp, F.Id("N"), Sp, F.Id("hN"), Sp, F.Id("s"), Sp, Eq, Sp, Parenthesized(Seq(Langle, Sp,
        Seq(Qualified(F.Id("s"), Dot, F.Id("natMod")), Sp, Parenthesized(new Formula.Apply(Qualified("Coe", "coe"),
        [F.Id("N")]))), Sp, Rangle)));

    private static Formula Statement18() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("N"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp,
        Parenthesized(Seq(F.Id("hN"), Sp, Colon, Sp, D(0), Sp, F.Lt, Sp, F.Id("N"))), Sp, Parenthesized(Seq(F.Id("s"),
        Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Call("val", Seq(Qualified(F.Id("FloorSelectorCycles"),
        Dot, F.Id("index")), Sp, F.Id("N"), Sp, F.Id("hN"), Sp, F.Id("s")))), Colon, Seq(Mathbb, Grp(F.Id("Z")))))), Sp, Eq, Sp, F.Id("s"), Sp,
        Qualified("HMod", "hMod"), Sp, Parenthesized(Parenthesized(Seq(F.Id("N"), Colon, Seq(Mathbb, Grp(F.Id("Z")))))));

    private static Formula Statement19() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("N"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp,
        Parenthesized(Seq(F.Id("hN"), Sp, Colon, Sp, D(0), Sp, F.Lt, Sp, F.Id("N"))), Sp, Parenthesized(Seq(F.Id("i"),
        Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("N"))), Sp, Comma, Sp, Qualified(F.Id("FloorSelectorCycles"), Dot,
        F.Id("index")), Sp, F.Id("N"), Sp, F.Id("hN"), Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Call("val", F.Id("i"))), Colon, Seq(Mathbb, Grp(F.Id("Z")))))), Sp, Eq, Sp, F.Id("i"));

    private static Formula Statement20() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("N"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp,
        Parenthesized(Seq(F.Id("hN"), Sp, Colon, Sp, D(0), Sp, F.Lt, Sp, F.Id("N"))), Sp, Parenthesized(Seq(F.Id("s"),
        Sp, F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Comma, Sp,
        Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("index")), Sp, F.Id("N"), Sp, F.Id("hN"), Sp,
        Parenthesized(Seq(F.Id("s"), Sp, Plus, Sp, F.Id("k"), Sp, Cdot, Sp, Parenthesized(new
        Formula.Apply(Qualified("Coe", "coe"), [F.Id("N")])))), Sp, Eq, Sp, Qualified(F.Id("FloorSelectorCycles"),
        Dot, F.Id("index")), Sp, F.Id("N"), Sp, F.Id("hN"), Sp, F.Id("s"));

    private static Formula Statement21() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("N"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp,
        Parenthesized(Seq(F.Id("hN"), Sp, Colon, Sp, D(0), Sp, F.Lt, Sp, F.Id("N"))), Sp, Parenthesized(Seq(F.Id("s"),
        Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Comma, Sp, Parenthesized(Call("val", Seq(Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("index")), Sp, F.Id("N"), Sp, F.Id("hN"), Sp,
        Parenthesized(Seq(F.Id("s"), Sp, Plus, Sp, D(1)))))), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Call("val", Seq(Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("index")), Sp,
        F.Id("N"), Sp, F.Id("hN"), Sp, F.Id("s")))), Sp, Plus, Sp, D(1))), Sp, Qualified("HMod", "hMod"), Sp,
        F.Id("N"));

    private static Formula Statement22() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("N"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp,
        Parenthesized(Seq(F.Id("hN"), Sp, Colon, Sp, D(0), Sp, F.Lt, Sp, F.Id("N"))), Sp, Parenthesized(Seq(F.Id("s"),
        Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Comma, Sp, Parenthesized(Call("val", Seq(Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("index")), Sp, F.Id("N"), Sp, F.Id("hN"), Sp,
        Parenthesized(Seq(F.Id("s"), Sp, Minus, Sp, D(1)))))), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Call("val", Seq(Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("index")), Sp,
        F.Id("N"), Sp, F.Id("hN"), Sp, F.Id("s")))), Sp, Plus, Sp, F.Id("N"), Sp, Minus, Sp, D(1))), Sp,
        Qualified("HMod", "hMod"), Sp, F.Id("N"));

    private static Formula Statement23() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("G"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp,
        Parenthesized(Seq(F.Id("hA"), Sp, Colon, Sp, D(0), Sp, F.Lt, Sp, F.Id("A"))), Sp,
        Parenthesized(Seq(F.Id("hG"), Sp, Colon, Sp, D(0), Sp, F.Lt, Sp, F.Id("G"))), Sp, Parenthesized(Seq(F.Id("a"),
        Sp, F.Id("b"), Sp, F.Id("s"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Comma, Sp,
        Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("orbit")), Sp, F.Id("A"), Sp, F.Id("G"), Sp, F.Id("hA"), Sp,
        F.Id("hG"), Sp, F.Id("a"), Sp, F.Id("b"), Sp, F.Id("s"), Sp, Eq, Sp,
        Parenthesized(Parenthesized(Seq(Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("index")), Sp, F.Id("A"), Sp,
        F.Id("hA"), Sp, Parenthesized(Seq(F.Id("a"), Sp, Minus, Sp, F.Id("s"))), Sp, Comma, Sp,
        Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("index")), Sp, F.Id("G"), Sp, F.Id("hG"), Sp,
        Parenthesized(Seq(F.Id("b"), Sp, Plus, Sp, F.Id("s")))))));

    private static Formula Statement24() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("G"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp,
        Parenthesized(Seq(F.Id("hG"), Sp, Colon, Sp, D(0), Sp, F.Lt, Sp, F.Id("G"))), Sp, Parenthesized(Seq(F.Id("s"),
        Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Comma, Sp, Qualified(F.Id("FloorSelectorCycles"), Dot,
        F.Id("edge")), Sp, F.Id("G"), Sp, F.Id("hG"), Sp, F.Id("s"), Sp, Eq, Sp, Parenthesized(Seq(F.Id("if"), Sp,
        Parenthesized(Call("val", Seq(Qualified(F.Id("FloorSelectorCycles"), Dot,
        F.Id("index")), Sp, F.Id("G"), Sp, F.Id("hG"), Sp, F.Id("s")))), Sp, Eq, Sp, D(0), Sp, F.Id("then"), Sp,
        D(1), Sp, Qualified("HDiv", "hDiv"), Sp, D(2), Sp, F.Id("else"), Sp, D(1))));

    private static Formula Statement25() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("G"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp,
        Parenthesized(Seq(F.Id("hA"), Sp, Colon, Sp, D(0), Sp, F.Lt, Sp, F.Id("A"))), Sp,
        Parenthesized(Seq(F.Id("hG"), Sp, Colon, Sp, D(0), Sp, F.Lt, Sp, F.Id("G"))), Sp, Parenthesized(Seq(F.Id("a"),
        Sp, F.Id("b"), Sp, F.Id("s"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Comma, Sp,
        Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("orbit")), Sp, F.Id("A"), Sp, F.Id("G"), Sp, F.Id("hA"), Sp,
        F.Id("hG"), Sp, F.Id("a"), Sp, F.Id("b"), Sp, Parenthesized(Seq(F.Id("s"), Sp, Plus, Sp, Parenthesized(new
        Formula.Apply(Qualified("Coe", "coe"), [F.Id("A")])), Sp, Cdot, Sp, Parenthesized(new
        Formula.Apply(Qualified("Coe", "coe"), [F.Id("G")])))), Sp, Eq, Sp, Qualified(F.Id("FloorSelectorCycles"),
        Dot, F.Id("orbit")), Sp, F.Id("A"), Sp, F.Id("G"), Sp, F.Id("hA"), Sp, F.Id("hG"), Sp, F.Id("a"), Sp,
        F.Id("b"), Sp, F.Id("s"));

    private static Formula Statement26() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("G"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp,
        Parenthesized(Seq(F.Id("hG"), Sp, Colon, Sp, D(0), Sp, F.Lt, Sp, F.Id("G"))), Sp, Parenthesized(Seq(F.Id("s"),
        Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Comma, Sp, D(0), Sp, F.Lt, Sp,
        Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("edge")), Sp, F.Id("G"), Sp, F.Id("hG"), Sp, F.Id("s"));

    private static Formula Statement27() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("G"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp,
        Parenthesized(Seq(F.Id("hA"), Sp, Colon, Sp, D(0), Sp, F.Lt, Sp, F.Id("A"))), Sp,
        Parenthesized(Seq(F.Id("hG"), Sp, Colon, Sp, D(0), Sp, F.Lt, Sp, F.Id("G"))), Sp, Parenthesized(Seq(F.Id("z"),
        Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("A"), Sp, Times, Sp, F.Id("Fin"), Sp, F.Id("G"), Sp, To, Sp, Seq(Mathbb,
        Grp(F.Id("Q"))))), Sp, Parenthesized(Seq(F.Id("a"), Sp, F.Id("b"), Sp, F.Id("s"), Sp, Colon, Sp, Seq(Mathbb,
        Grp(F.Id("Z"))))), Sp, Comma, Sp, Parenthesized(Seq(Parenthesized(Seq(Qualified(F.Id("FloorSelectorCycles"),
        Dot, F.Id("backward")), Sp, F.Id("A"))), Sp, Dot, Sp, F.Id("kronecker"), Sp,
        Parenthesized(Seq(Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("forwardHalf")), Sp, F.Id("G"))))), Sp,
        Dot, Sp, F.Id("mulVec"), Sp, F.Id("z"), Sp, Parenthesized(Seq(Qualified(F.Id("FloorSelectorCycles"), Dot,
        F.Id("orbit")), Sp, F.Id("A"), Sp, F.Id("G"), Sp, F.Id("hA"), Sp, F.Id("hG"), Sp, F.Id("a"), Sp, F.Id("b"),
        Sp, F.Id("s"))), Sp, Eq, Sp, Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("edge")), Sp, F.Id("G"), Sp,
        F.Id("hG"), Sp, Parenthesized(Seq(F.Id("b"), Sp, Plus, Sp, F.Id("s"))), Sp, Cdot, Sp, F.Id("z"), Sp,
        Parenthesized(Seq(Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("orbit")), Sp, F.Id("A"), Sp, F.Id("G"),
        Sp, F.Id("hA"), Sp, F.Id("hG"), Sp, F.Id("a"), Sp, F.Id("b"), Sp, Parenthesized(Seq(F.Id("s"), Sp, Minus, Sp,
        D(1))))));

    private static Formula Statement28() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("B"), Sp, F.Id("G"), Sp, F.Id("D"), Sp, Colon, Sp,
        Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, D(0), Sp, F.Lt, Sp, F.Id("A"), Sp, To, Sp, D(0), Sp, F.Lt, Sp,
        F.Id("G"), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("phaseI"), Sp, F.Id("phaseO"), Sp, Colon, Sp,
        Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Comma, Sp, Seq(new Formula.Subscript(Sum, Seq(F.Id("t"), Sp, InMacro, Sp,
        Qualified(F.Id("Finset"), Dot, F.Id("range")), Sp, Parenthesized(Seq(F.Id("A"), Sp, Cdot, Sp, F.Id("G"))))),
        Sp, Parenthesized(Parenthesized(Seq(Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("jump")), Sp,
        Parenthesized(Seq(Parenthesized(new Formula.Apply(Qualified("Coe", "coe"), [F.Id("D")])), Sp,
        Qualified("HDiv", "hDiv"), Sp, Parenthesized(new Formula.Apply(Qualified("Coe", "coe"), [F.Id("G")])))), Sp,
        Parenthesized(Seq(F.Id("phaseI"), Sp, Plus, Sp, Parenthesized(new Formula.Apply(Qualified("Coe", "coe"),
        [F.Id("t")])))), Sp, Minus, Sp, Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("jump")), Sp,
        Parenthesized(Seq(Parenthesized(new Formula.Apply(Qualified("Coe", "coe"), [F.Id("B")])), Sp,
        Qualified("HDiv", "hDiv"), Sp, Parenthesized(new Formula.Apply(Qualified("Coe", "coe"), [F.Id("A")])))), Sp,
        Parenthesized(Seq(F.Id("phaseO"), Sp, Minus, Sp, Parenthesized(new Formula.Apply(Qualified("Coe", "coe"),
        [F.Id("t")])))))))), Sp, Eq, Sp, Parenthesized(new Formula.Apply(Qualified("Coe", "coe"), [Seq(F.Id("A"), Sp,
        Cdot, Sp, F.Id("D"))])), Sp, Minus, Sp, Parenthesized(new Formula.Apply(Qualified("Coe", "coe"),
        [Seq(F.Id("G"), Sp, Cdot, Sp, F.Id("B"))])));

    private static Formula Statement29() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("B"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp,
        Parenthesized(Seq(F.Id("hA"), Sp, Colon, Sp, D(0), Sp, F.Lt, Sp, F.Id("A"))), Sp, Parenthesized(Seq(F.Id("s"),
        Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Comma, Sp, Qualified(F.Id("FloorSelectorCycles"), Dot,
        F.Id("jump")), Sp, Parenthesized(Seq(Parenthesized(Parenthesized(Seq(F.Id("B"), Colon, Seq(Mathbb, Grp(F.Id("Q")))))),
        Sp, Qualified("HDiv", "hDiv"), Sp, Parenthesized(Parenthesized(Seq(F.Id("A"), Colon, Seq(Mathbb, Grp(F.Id("Q")))))))),
        Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Call("val", Seq(Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("index")), Sp, F.Id("A"), Sp, F.Id("hA"), Sp,
        F.Id("s")))), Colon, Seq(Mathbb, Grp(F.Id("Z")))))), Sp, Eq, Sp, Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("jump")), Sp,
        Parenthesized(Seq(Parenthesized(Parenthesized(Seq(F.Id("B"), Colon, Seq(Mathbb, Grp(F.Id("Q")))))), Sp,
        Qualified("HDiv", "hDiv"), Sp, Parenthesized(Parenthesized(Seq(F.Id("A"), Colon, Seq(Mathbb, Grp(F.Id("Q")))))))), Sp,
        F.Id("s"));

    private static Formula Statement30() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("G"), Sp, F.Id("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp,
        Parenthesized(Seq(F.Id("hG"), Sp, Colon, Sp, D(0), Sp, F.Lt, Sp, F.Id("G"))), Sp,
        Parenthesized(Seq(F.Id("phase"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Comma, Sp, Seq(new
        Formula.Subscript(Prod, Seq(F.Id("t"), Sp, InMacro, Sp, Qualified(F.Id("Finset"), Dot, F.Id("range")), Sp,
        Parenthesized(Seq(F.Id("M"), Sp, Cdot, Sp, F.Id("G"))))), Sp,
        Parenthesized(Seq(Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("edge")), Sp, F.Id("G"), Sp, F.Id("hG"),
        Sp, Parenthesized(Seq(F.Id("phase"), Sp, Plus, Sp, Parenthesized(new Formula.Apply(Qualified("Coe", "coe"),
        [F.Id("t")]))))))), Sp, Eq, Sp, new Formula.Power(Parenthesized(Seq(D(1), Sp, Qualified("HDiv", "hDiv"), Sp,
        D(2))), F.Id("M")));

    private static Formula Statement31() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("G"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp,
        Comma, Sp, D(0), Sp, F.Lt, Sp, F.Id("A"), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("hG"), Sp, Colon, Sp,
        D(0), Sp, F.Lt, Sp, F.Id("G"))), Sp, Parenthesized(Seq(F.Id("phase"), Sp, Colon, Sp, Seq(Mathbb,
        Grp(F.Id("Z"))))), Sp, Comma, Sp, Seq(new Formula.Subscript(Prod, Seq(F.Id("t"), Sp, InMacro, Sp,
        Qualified(F.Id("Finset"), Dot, F.Id("range")), Sp, Parenthesized(Seq(F.Id("A"), Sp, Cdot, Sp, F.Id("G"))))),
        Sp, Parenthesized(Seq(Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("edge")), Sp, F.Id("G"), Sp,
        F.Id("hG"), Sp, Parenthesized(Seq(F.Id("phase"), Sp, Plus, Sp, Parenthesized(new
        Formula.Apply(Qualified("Coe", "coe"), [F.Id("t")])), Sp, Plus, Sp, D(1)))))), Sp, F.Lt, Sp, D(1));

}
