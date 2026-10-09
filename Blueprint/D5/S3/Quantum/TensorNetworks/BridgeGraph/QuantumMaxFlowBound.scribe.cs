using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.BridgeGraph;

internal sealed class QuantumMaxFlowBoundDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound";
    private static readonly LibraryNoteRef Paper = LibraryNoteRef.Create("D5/L/QuantumBounds/gesmundo2025bridge");
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Qualified(params Formula[] names) => Seq(Operatorname, Grp(names));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "QuantumMaxFlowBound supplies the width-three bridge max-flow proof.",
        H("QuantumMaxFlowBound"), Blocks(
            Paragraph(Text("Formulas retain the Lean parameter types and all hypotheses. HDiv.hDiv and HMod.hMod are displayed infix: on natural and integer carriers they mean the respective Lean integer division and remainder operations; on rational carriers division is field division. Coe.coe denotes the coercion determined by the displayed target type. Finite and dependent-pair constructors omit proof fields, which do not change their values. A dash in a match pattern is an anonymous wildcard. CoeFun.coe and CoeSort.coe retain coercions to functions and types. All dimensions use ℕ, all construction coefficients use ℚ, and max-flow uses ℂ.")),
            Describe.Lean(DescribeId.Create("gls-quantummaxflowbound-flow"),
                DeclarationHandle.Create(Owner + ".flow"),
                H("flow"), StatementSource.FromAuthor(Disp(Statement0())),
                AssessedProvenance.FromLiterature(Paper),
                Blocks(Paragraph(Text("Page 3: “Let F_{T,T′} ∈ A ⊗ B ⊗ A′ ⊗ B′ be the tensor obtained by contracting the factor W of T with the factor W* of T′; this is the tensor network state defined by T and T′ on the bridge graph.” For width three the flow matrix is the sum of three Kronecker products. Its dimensions are a*d by b*c. With (a,b,c,d)=(a,b,a′,b′), it is the transpose of the source flattening (A ⊗ B′)* → B ⊗ A′; transpose preserves rank."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gls-quantummaxflowbound-attainable"),
                DeclarationHandle.Create(Owner + ".attainable"),
                H("attainable"), StatementSource.FromAuthor(Disp(Statement1())),
                AssessedProvenance.FromLiterature(Paper),
                Blocks(Paragraph(Text("Attainable is the set of natural ranks of the literal width-three complex flow matrices."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gls-quantummaxflowbound-qmaxflow"),
                DeclarationHandle.Create(Owner + ".QMaxFlow"),
                H("QMaxFlow"), StatementSource.FromAuthor(Disp(Statement2())),
                AssessedProvenance.FromLiterature(Paper),
                Blocks(Paragraph(Text("Page 3: “The quantum max-flow is the maximum possible value of rank(F_{T,T′}) as T and T′ vary in the respective spaces; we write”. The source then displays the maximum over T ∈ A ⊗ B ⊗ W and T′ ∈ A′ ⊗ B′ ⊗ W*. Here the attained supremum of the finite nonempty natural rank set gives that maximum."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gls-quantummaxflowbound-qmincut"),
                DeclarationHandle.Create(Owner + ".QMinCut"),
                H("QMinCut"), StatementSource.FromAuthor(Disp(Statement3())),
                AssessedProvenance.FromLiterature(Paper),
                Blocks(Paragraph(Text("Proposition 2.4, page 9: “Let a, b, w, a′, b′ be integers with a ≤ b, a′ ≤ b′. The quantum min-cut in the bridge graph is” followed by QMinCut = min{aa′w, ab′, a′b}. This is the ordered-case cut formula: its identification with the graph min-cut is used under a ≤ b and c ≤ d, as in claim. The Lean letters (a,b,c,d) denote (a,b,a′,b′) and the bridge width is three."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gls-quantummaxflowbound-qmaxflow-attained"),
                DeclarationHandle.Create(Owner + ".QMaxFlow_attained"),
                H("QMaxFlow_attained"), StatementSource.FromAuthor(Disp(Statement4())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("QMaxFlow_attained is used on the live proof path of the width-three bridge construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-quantummaxflowbound-rank-le-qmaxflow"),
                DeclarationHandle.Create(Owner + ".rank_le_QMaxFlow"),
                H("rank_le_QMaxFlow"), StatementSource.FromAuthor(Disp(Statement5())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("rank_le_QMaxFlow is used on the live proof path of the width-three bridge construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-quantummaxflowbound-qmaxflow-le-qmincut"),
                DeclarationHandle.Create(Owner + ".QMaxFlow_le_QMinCut"),
                H("QMaxFlow_le_QMinCut"), StatementSource.FromAuthor(Disp(Statement7())),
                AssessedProvenance.FromLiterature(Paper),
                Blocks(Paragraph(Text("QMaxFlow_le_QMinCut is used on the live proof path of the width-three bridge construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-quantummaxflowbound-cone-bounds"),
                DeclarationHandle.Create(Owner + ".cone_bounds"),
                H("cone_bounds"), StatementSource.FromAuthor(Disp(Statement8())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("cone_bounds is used on the live proof path of the width-three bridge construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-quantummaxflowbound-cone-qmincut"),
                DeclarationHandle.Create(Owner + ".cone_QMinCut"),
                H("cone_QMinCut"), StatementSource.FromAuthor(Disp(Statement9())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("cone_QMinCut is used on the live proof path of the width-three bridge construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-quantummaxflowbound-rationalwitness"),
                DeclarationHandle.Create(Owner + ".RationalWitness"),
                H("RationalWitness"), StatementSource.FromAuthor(Disp(Statement10())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The defining expression fixes RationalWitness for the consumed QuantumMaxFlowBound construction."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gls-quantummaxflowbound-rationalwitness-full-rank"),
                DeclarationHandle.Create(Owner + ".rationalWitness_full_rank"),
                H("rationalWitness_full_rank"), StatementSource.FromAuthor(Disp(Statement11())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("rationalWitness_full_rank is used on the live proof path of the width-three bridge construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-quantummaxflowbound-basewitness"),
                DeclarationHandle.Create(Owner + ".BaseWitness"),
                H("BaseWitness"), StatementSource.FromAuthor(Disp(Statement12())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The defining expression fixes BaseWitness for the consumed QuantumMaxFlowBound construction."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gls-quantummaxflowbound-castling"),
                DeclarationHandle.Create(Owner + ".Castling"),
                H("Castling"), StatementSource.FromAuthor(Disp(Statement13())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The defining expression fixes Castling for the consumed QuantumMaxFlowBound construction."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gls-quantummaxflowbound-widthtwo"),
                DeclarationHandle.Create(Owner + ".WidthTwo"),
                H("WidthTwo"), StatementSource.FromAuthor(Disp(Statement14())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The defining expression fixes WidthTwo for the consumed QuantumMaxFlowBound construction."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gls-quantummaxflowbound-threeslices"),
                DeclarationHandle.Create(Owner + ".threeSlices"),
                H("threeSlices"), StatementSource.FromAuthor(Disp(Statement15())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The defining expression fixes threeSlices for the consumed QuantumMaxFlowBound construction."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gls-quantummaxflowbound-typed-three-slice-flow"),
                DeclarationHandle.Create(Owner + ".typed_three_slice_flow"),
                H("typed_three_slice_flow"), StatementSource.FromAuthor(Disp(Statement16())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("typed_three_slice_flow is used on the live proof path of the width-three bridge construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-quantummaxflowbound-rectid"),
                DeclarationHandle.Create(Owner + ".rectId"),
                H("rectId"), StatementSource.FromAuthor(Disp(Statement17())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The defining expression fixes rectId for the consumed QuantumMaxFlowBound construction."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gls-quantummaxflowbound-witness-swap"),
                DeclarationHandle.Create(Owner + ".witness_swap"),
                H("witness_swap"), StatementSource.FromAuthor(Disp(Statement18())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("witness_swap is used on the live proof path of the width-three bridge construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-quantummaxflowbound-widthtwo-proved"),
                DeclarationHandle.Create(Owner + ".widthTwo_proved"),
                H("widthTwo_proved"), StatementSource.FromAuthor(Disp(Statement19())),
                AssessedProvenance.FromLiterature(Paper),
                Blocks(Paragraph(Text("widthTwo_proved is used on the live proof path of the width-three bridge construction."))),
                DescribeRole.Theorem))));

    private static Formula Statement0() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("K"), Sp, Colon, Sp, F.Id("Type"))), Sp, Seq(OpenBracket,
        Seq(F.Id("CommSemiring"), Sp, F.Id("K")), CloseBracket), Sp, Parenthesized(Seq(F.Id("a"), Sp, F.Id("b"), Sp,
        F.Id("c"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("M"), Sp,
        Colon, Sp, F.Id("Fin"), Sp, D(3), Sp, To, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp,
        F.Id("a"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("b"))), Sp, F.Id("K"))), Sp,
        Parenthesized(Seq(F.Id("N"), Sp, Colon, Sp, F.Id("Fin"), Sp, D(3), Sp, To, Sp, F.Id("Matrix"), Sp,
        Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("c"))), Sp,
        F.Id("K"))), Sp, Comma, Sp, Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("flow")), Sp, F.Id("M"), Sp,
        F.Id("N"), Sp, Eq, Sp, Parenthesized(Seq(new Formula.Subscript(Sum, Seq(F.Id("r"), Sp, Colon, Sp, F.Id("Fin"),
        Sp, D(3))), Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("M"), Sp, F.Id("r"))), Sp, Dot, Sp,
        F.Id("kronecker"), Sp, Parenthesized(Seq(F.Id("N"), Sp, F.Id("r"))))))));

    private static Formula Statement1() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("a"), Sp, F.Id("b"), Sp, F.Id("c"), Sp, F.Id("d"), Sp, Colon, Sp,
        Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("attainable")),
        Sp, F.Id("a"), Sp, F.Id("b"), Sp, F.Id("c"), Sp, F.Id("d"), Sp, Eq, Sp, Parenthesized(Seq(OpenBrace,
        Seq(F.Id("r"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Bar, Sp, Exists, Sp,
        Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, F.Id("Fin"), Sp, D(3), Sp, To, Sp, F.Id("Matrix"), Sp,
        Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("a"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("b"))), Sp,
        Seq(Mathbb, Grp(F.Id("C"))))), Sp, Parenthesized(Seq(F.Id("N"), Sp, Colon, Sp, F.Id("Fin"), Sp, D(3), Sp, To,
        Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp,
        F.Id("c"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Comma, Sp,
        Parenthesized(Seq(Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("flow")), Sp, F.Id("M"), Sp, F.Id("N"))),
        Sp, Dot, Sp, F.Id("rank"), Sp, Eq, Sp, F.Id("r")), CloseBrace)));

    private static Formula Statement2() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("a"), Sp, F.Id("b"), Sp, F.Id("c"), Sp, F.Id("d"), Sp, Colon, Sp,
        Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("QMaxFlow")),
        Sp, F.Id("a"), Sp, F.Id("b"), Sp, F.Id("c"), Sp, F.Id("d"), Sp, Eq, Sp, Parenthesized(Seq(F.Id("sSup"), Sp,
        Parenthesized(Seq(Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("attainable")), Sp, F.Id("a"), Sp,
        F.Id("b"), Sp, F.Id("c"), Sp, F.Id("d"))))));

    private static Formula Statement3() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("a"), Sp, F.Id("b"), Sp, F.Id("c"), Sp, F.Id("d"), Sp, Colon, Sp,
        Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("QMinCut")),
        Sp, F.Id("a"), Sp, F.Id("b"), Sp, F.Id("c"), Sp, F.Id("d"), Sp, Eq, Sp, Parenthesized(Seq(F.Id("min"), Sp,
        Parenthesized(Seq(D(3), Sp, Cdot, Sp, F.Id("a"), Sp, Cdot, Sp, F.Id("c"))), Sp, Parenthesized(Seq(F.Id("min"),
        Sp, Parenthesized(Seq(F.Id("a"), Sp, Cdot, Sp, F.Id("d"))), Sp, Parenthesized(Seq(F.Id("b"), Sp, Cdot, Sp,
        F.Id("c"))))))));

    private static Formula Statement4() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("a"), Sp, F.Id("b"), Sp, F.Id("c"), Sp, F.Id("d"), Sp, Colon, Sp,
        Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Exists, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp,
        F.Id("Fin"), Sp, D(3), Sp, To, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("a"))), Sp,
        Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("b"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp,
        Parenthesized(Seq(F.Id("N"), Sp, Colon, Sp, F.Id("Fin"), Sp, D(3), Sp, To, Sp, F.Id("Matrix"), Sp,
        Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("c"))), Sp,
        Seq(Mathbb, Grp(F.Id("C"))))), Sp, Comma, Sp, Parenthesized(Seq(Qualified(F.Id("QuantumMaxFlowBound"), Dot,
        F.Id("flow")), Sp, F.Id("M"), Sp, F.Id("N"))), Sp, Dot, Sp, F.Id("rank"), Sp, Eq, Sp,
        Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("QMaxFlow")), Sp, F.Id("a"), Sp, F.Id("b"), Sp, F.Id("c"),
        Sp, F.Id("d"));

    private static Formula Statement5() =>
        Seq(Forall, Sp, Seq(OpenBrace, Seq(F.Id("a"), Sp, F.Id("b"), Sp, F.Id("c"), Sp, F.Id("d"), Sp, Colon, Sp,
        Seq(Mathbb, Grp(F.Id("N")))), CloseBrace), Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, F.Id("Fin"), Sp,
        D(3), Sp, To, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("a"))), Sp,
        Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("b"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp,
        Parenthesized(Seq(F.Id("N"), Sp, Colon, Sp, F.Id("Fin"), Sp, D(3), Sp, To, Sp, F.Id("Matrix"), Sp,
        Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("c"))), Sp,
        Seq(Mathbb, Grp(F.Id("C"))))), Sp, Comma, Sp, Parenthesized(Seq(Qualified(F.Id("QuantumMaxFlowBound"), Dot,
        F.Id("flow")), Sp, F.Id("M"), Sp, F.Id("N"))), Sp, Dot, Sp, F.Id("rank"), Sp, Leq, Sp,
        Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("QMaxFlow")), Sp, F.Id("a"), Sp, F.Id("b"), Sp, F.Id("c"),
        Sp, F.Id("d"));

    private static Formula Statement7() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("a"), Sp, F.Id("b"), Sp, F.Id("c"), Sp, F.Id("d"), Sp, Colon, Sp,
        Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("QMaxFlow")),
        Sp, F.Id("a"), Sp, F.Id("b"), Sp, F.Id("c"), Sp, F.Id("d"), Sp, Leq, Sp,
        Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("QMinCut")), Sp, F.Id("a"), Sp, F.Id("b"), Sp, F.Id("c"), Sp,
        F.Id("d"));

    private static Formula Statement8() =>
        Seq(Forall, Sp, Seq(OpenBrace, Seq(F.Id("a"), Sp, F.Id("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))),
        CloseBrace), Sp, Comma, Sp, D(0), Sp, F.Lt, Sp, F.Id("a"), Sp, To, Sp, F.Id("a"), Sp, Cdot, Sp, F.Id("a"), Sp,
        Plus, Sp, F.Id("b"), Sp, Cdot, Sp, F.Id("b"), Sp, Leq, Sp, D(3), Sp, Cdot, Sp, F.Id("a"), Sp, Cdot, Sp,
        F.Id("b"), Sp, To, Sp, F.Id("b"), Sp, F.Lt, Sp, D(3), Sp, Cdot, Sp, F.Id("a"));

    private static Formula Statement9() =>
        Seq(Forall, Sp, Seq(OpenBrace, Seq(F.Id("a"), Sp, F.Id("b"), Sp, F.Id("c"), Sp, F.Id("d"), Sp, Colon, Sp,
        Seq(Mathbb, Grp(F.Id("N")))), CloseBrace), Sp, Comma, Sp, D(0), Sp, F.Lt, Sp, F.Id("a"), Sp, To, Sp, D(0), Sp,
        F.Lt, Sp, F.Id("c"), Sp, To, Sp, F.Id("a"), Sp, Cdot, Sp, F.Id("a"), Sp, Plus, Sp, F.Id("b"), Sp, Cdot, Sp,
        F.Id("b"), Sp, Leq, Sp, D(3), Sp, Cdot, Sp, F.Id("a"), Sp, Cdot, Sp, F.Id("b"), Sp, To, Sp, F.Id("c"), Sp,
        Cdot, Sp, F.Id("c"), Sp, Plus, Sp, F.Id("d"), Sp, Cdot, Sp, F.Id("d"), Sp, Leq, Sp, D(3), Sp, Cdot, Sp,
        F.Id("c"), Sp, Cdot, Sp, F.Id("d"), Sp, To, Sp, Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("QMinCut")),
        Sp, F.Id("a"), Sp, F.Id("b"), Sp, F.Id("c"), Sp, F.Id("d"), Sp, Eq, Sp, F.Id("min"), Sp,
        Parenthesized(Seq(F.Id("a"), Sp, Cdot, Sp, F.Id("d"))), Sp, Parenthesized(Seq(F.Id("b"), Sp, Cdot, Sp,
        F.Id("c"))));

    private static Formula Statement10() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("a"), Sp, F.Id("b"), Sp, F.Id("c"), Sp, F.Id("d"), Sp, Colon, Sp,
        Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Qualified(F.Id("QuantumMaxFlowBound"), Dot,
        F.Id("RationalWitness")), Sp, F.Id("a"), Sp, F.Id("b"), Sp, F.Id("c"), Sp, F.Id("d"), Sp, Eq, Sp,
        Parenthesized(Seq(Exists, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, F.Id("Fin"), Sp, D(3), Sp, To, Sp,
        F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("a"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp,
        F.Id("b"))), Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Parenthesized(Seq(F.Id("N"), Sp, Colon, Sp, F.Id("Fin"),
        Sp, D(3), Sp, To, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("d"))), Sp,
        Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("c"))), Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Comma, Sp,
        Parenthesized(Seq(Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("flow")), Sp, F.Id("M"), Sp, F.Id("N"))),
        Sp, Dot, Sp, F.Id("rank"), Sp, Eq, Sp, F.Id("min"), Sp, Parenthesized(Seq(F.Id("a"), Sp, Cdot, Sp,
        F.Id("d"))), Sp, Parenthesized(Seq(F.Id("b"), Sp, Cdot, Sp, F.Id("c"))))));

    private static Formula Statement11() =>
        Seq(Forall, Sp, Seq(OpenBrace, Seq(F.Id("a"), Sp, F.Id("b"), Sp, F.Id("c"), Sp, F.Id("d"), Sp, Colon, Sp,
        Seq(Mathbb, Grp(F.Id("N")))), CloseBrace), Sp, Comma, Sp, Qualified(F.Id("QuantumMaxFlowBound"), Dot,
        F.Id("RationalWitness")), Sp, F.Id("a"), Sp, F.Id("b"), Sp, F.Id("c"), Sp, F.Id("d"), Sp, To, Sp,
        Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("QMaxFlow")), Sp, F.Id("a"), Sp, F.Id("b"), Sp, F.Id("c"),
        Sp, F.Id("d"), Sp, Eq, Sp, F.Id("min"), Sp, Parenthesized(Seq(F.Id("a"), Sp, Cdot, Sp, F.Id("d"))), Sp,
        Parenthesized(Seq(F.Id("b"), Sp, Cdot, Sp, F.Id("c"))));

    private static Formula Statement12() =>
        Seq(Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("BaseWitness")), Sp, Iff, Sp, Parenthesized(Seq(Forall,
        Sp, Parenthesized(Seq(F.Id("a"), Sp, F.Id("b"), Sp, F.Id("c"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb,
        Grp(F.Id("N"))))), Sp, Comma, Sp, D(0), Sp, F.Lt, Sp, F.Id("a"), Sp, To, Sp, F.Id("a"), Sp, F.Lt, Sp,
        F.Id("b"), Sp, To, Sp, F.Id("b"), Sp, F.Lt, Sp, D(2), Sp, Cdot, Sp, F.Id("a"), Sp, To, Sp, D(0), Sp, F.Lt, Sp,
        F.Id("c"), Sp, To, Sp, F.Id("c"), Sp, F.Lt, Sp, F.Id("d"), Sp, To, Sp, F.Id("d"), Sp, F.Lt, Sp, D(2), Sp,
        Cdot, Sp, F.Id("c"), Sp, To, Sp, Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("RationalWitness")), Sp,
        F.Id("a"), Sp, F.Id("b"), Sp, F.Id("c"), Sp, F.Id("d"))));

    private static Formula Statement13() =>
        Seq(Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("Castling")), Sp, Iff, Sp, Parenthesized(Seq(Forall, Sp,
        Parenthesized(Seq(F.Id("a"), Sp, F.Id("b"), Sp, F.Id("c"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb,
        Grp(F.Id("N"))))), Sp, Comma, Sp, F.Id("a"), Sp, Leq, Sp, D(3), Sp, Cdot, Sp, F.Id("b"), Sp, To, Sp,
        F.Id("c"), Sp, Leq, Sp, D(3), Sp, Cdot, Sp, F.Id("d"), Sp, To, Sp,
        Parenthesized(Seq(Parenthesized(Seq(F.Id("a"), Sp, Cdot, Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb,
        Grp(F.Id("N"))))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Minus, Sp,
        Parenthesized(Seq(Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("QMaxFlow")), Sp, F.Id("a"), Sp, F.Id("b"),
        Sp, F.Id("c"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Eq, Sp,
        Parenthesized(Seq(Parenthesized(Seq(F.Id("b"), Sp, Cdot, Sp, Parenthesized(Seq(D(3), Sp, Cdot, Sp, F.Id("d"),
        Sp, Minus, Sp, F.Id("c"))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Colon, Sp, Seq(Mathbb,
        Grp(F.Id("Z"))))), Sp, Minus, Sp, Parenthesized(Seq(Qualified(F.Id("QuantumMaxFlowBound"), Dot,
        F.Id("QMaxFlow")), Sp, F.Id("b"), Sp, Parenthesized(Seq(D(3), Sp, Cdot, Sp, F.Id("b"), Sp, Minus, Sp,
        F.Id("a"))), Sp, F.Id("d"), Sp, Parenthesized(Seq(D(3), Sp, Cdot, Sp, F.Id("d"), Sp, Minus, Sp, F.Id("c"))),
        Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))))));

    private static Formula Statement14() =>
        Seq(Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("WidthTwo")), Sp, Iff, Sp, Parenthesized(Seq(Forall, Sp,
        Parenthesized(Seq(F.Id("a"), Sp, F.Id("b"), Sp, F.Id("c"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb,
        Grp(F.Id("N"))))), Sp, Comma, Sp, D(0), Sp, F.Lt, Sp, F.Id("a"), Sp, To, Sp, F.Id("a"), Sp, Leq, Sp,
        F.Id("b"), Sp, To, Sp, D(0), Sp, F.Lt, Sp, F.Id("c"), Sp, To, Sp, F.Id("c"), Sp, Leq, Sp, F.Id("d"), Sp, To,
        Sp, Parenthesized(Seq(
            F.Id("a"), Sp, Eq, Sp, F.Id("b"), Sp, Lor, Sp,
            F.Id("c"), Sp, Eq, Sp, F.Id("d"), Sp, Lor, Sp,
            Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("a"), Sp, Leq, Sp, F.Id("b"), Sp, Land, Sp,
                F.Id("d"), Sp, Leq, Sp, D(2), Sp, Cdot, Sp, F.Id("c"))), Sp, Lor, Sp,
            Parenthesized(Seq(F.Id("b"), Sp, Leq, Sp, D(2), Sp, Cdot, Sp, F.Id("a"), Sp, Land, Sp,
                D(2), Sp, Cdot, Sp, F.Id("c"), Sp, Leq, Sp, F.Id("d"))))), Sp, To, Sp, Qualified(F.Id("QuantumMaxFlowBound"), Dot,
        F.Id("RationalWitness")), Sp, F.Id("a"), Sp, F.Id("b"), Sp, F.Id("c"), Sp, F.Id("d"))));

    private static Formula Statement15() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, F.Id("Type"))), Sp, Parenthesized(Seq(F.Id("n"),
        Sp, Colon, Sp, F.Id("Type"))), Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("B"), Sp, F.Id("C"), Sp, Colon, Sp,
        F.Id("Matrix"), Sp, F.Id("m"), Sp, F.Id("n"), Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp,
        Parenthesized(Seq(F.Id("r"), Sp, Colon, Sp, F.Id("Fin"), Sp, D(3))), Sp, Comma, Sp,
        Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("threeSlices")), Sp, F.Id("A"), Sp, F.Id("B"), Sp, F.Id("C"),
        Sp, F.Id("r"), Sp, Eq, Sp, Parenthesized(Seq(F.Id("if"), Sp, F.Id("r"), Sp, Eq, Sp, D(0), Sp, F.Id("then"),
        Sp, F.Id("A"), Sp, F.Id("else"), Sp, F.Id("if"), Sp, F.Id("r"), Sp, Eq, Sp, D(1), Sp, F.Id("then"), Sp,
        F.Id("B"), Sp, F.Id("else"), Sp, F.Id("C"))));

    private static Formula Statement16() =>
        Seq(Forall, Sp, Seq(OpenBrace, Seq(F.Id("I"), Sp, Colon, Sp, F.Id("Type")), CloseBrace), Sp, Seq(OpenBrace,
        Seq(F.Id("J"), Sp, Colon, Sp, F.Id("Type")), CloseBrace), Sp, Seq(OpenBrace, Seq(F.Id("K"), Sp, Colon, Sp,
        F.Id("Type")), CloseBrace), Sp, Seq(OpenBrace, Seq(F.Id("L"), Sp, Colon, Sp, F.Id("Type")), CloseBrace), Sp,
        Parenthesized(Seq(F.Id("A"), Sp, F.Id("B"), Sp, F.Id("C"), Sp, Colon, Sp, F.Id("Matrix"), Sp, F.Id("I"), Sp,
        F.Id("J"), Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Parenthesized(Seq(F.Id("D"), Sp, F.Id("E"), Sp, F.Id("F"),
        Sp, Colon, Sp, F.Id("Matrix"), Sp, F.Id("L"), Sp, F.Id("K"), Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Comma, Sp,
        Seq(new Formula.Subscript(Sum, Seq(F.Id("r"), Sp, Colon, Sp, F.Id("Fin"), Sp, D(3))), Sp,
        Parenthesized(Seq(Parenthesized(Seq(Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("threeSlices")), Sp,
        F.Id("A"), Sp, F.Id("B"), Sp, F.Id("C"), Sp, F.Id("r"))), Sp, Dot, Sp, F.Id("kronecker"), Sp,
        Parenthesized(Seq(Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("threeSlices")), Sp, F.Id("D"), Sp,
        F.Id("E"), Sp, F.Id("F"), Sp, F.Id("r")))))), Sp, Eq, Sp, Qualified(F.Id("A"), Dot, F.Id("kronecker")), Sp,
        F.Id("D"), Sp, Plus, Sp, Qualified(F.Id("B"), Dot, F.Id("kronecker")), Sp, F.Id("E"), Sp, Plus, Sp,
        Qualified(F.Id("C"), Dot, F.Id("kronecker")), Sp, F.Id("F"));

    private static Formula Statement17() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("m"), Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp,
        Comma, Sp, Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("rectId")), Sp, F.Id("m"), Sp, F.Id("n"), Sp, Eq,
        Sp, Parenthesized(Seq(Qualified(F.Id("Matrix"), Dot, F.Id("submatrix")), Sp, D(1), Sp, Qualified(F.Id("Fin"),
        Dot, F.Id("val")), Sp, Qualified(F.Id("Fin"), Dot, F.Id("val")))));

    private static Formula Statement18() =>
        Seq(Forall, Sp, Seq(OpenBrace, Seq(F.Id("a"), Sp, F.Id("b"), Sp, F.Id("c"), Sp, F.Id("d"), Sp, Colon, Sp,
        Seq(Mathbb, Grp(F.Id("N")))), CloseBrace), Sp, Comma, Sp, Qualified(F.Id("QuantumMaxFlowBound"), Dot,
        F.Id("RationalWitness")), Sp, F.Id("a"), Sp, F.Id("b"), Sp, F.Id("c"), Sp, F.Id("d"), Sp, To, Sp,
        Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("RationalWitness")), Sp, F.Id("c"), Sp, F.Id("d"), Sp,
        F.Id("a"), Sp, F.Id("b"));

    private static Formula Statement19() =>
        Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("WidthTwo"));

}
