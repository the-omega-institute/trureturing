using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.BridgeGraph;

internal sealed class ShiftPencilBlocksDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks";
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Qualified(string owner, string name) =>
        Qualified(F.Id(owner), Dot, F.Id(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula Qualified(params Formula[] names) => Seq(Operatorname, Grp(names));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "ShiftPencilBlocks supplies the width-three bridge max-flow proof.",
        H("ShiftPencilBlocks"), Blocks(
            Paragraph(Text("Formulas retain the Lean parameter types and all hypotheses. HDiv.hDiv and HMod.hMod are displayed infix: on natural and integer carriers they mean the respective Lean integer division and remainder operations; on rational carriers division is field division. Coe.coe denotes the coercion determined by the displayed target type. Finite and dependent-pair constructors omit proof fields, which do not change their values. A dash in a match pattern is an anonymous wildcard. CoeFun.coe and CoeSort.coe retain coercions to functions and types. All dimensions use ℕ, all construction coefficients use ℚ, and max-flow uses ℂ.")),
            Describe.Lean(DescribeId.Create("gls-shiftpencilblocks-parameterizedbasewitness"),
                DeclarationHandle.Create(Owner + ".ParameterizedBaseWitness"),
                H("ParameterizedBaseWitness"), StatementSource.FromAuthor(Disp(Statement0())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("ParameterizedBaseWitness asserts rational full-rank flows for pairs whose dimensions are sums of short and long shift-block dimensions, with positive depths and positive long-block multiplicities; base_of_parameterized uses the decomposition of strict base pairs to recover BaseWitness."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gls-shiftpencilblocks-base-of-parameterized"),
                DeclarationHandle.Create(Owner + ".base_of_parameterized"),
                H("base_of_parameterized"), StatementSource.FromAuthor(Disp(Statement1())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every strict base dimension pair can be decomposed into short and long shift blocks, so full rank for the parameterized family implies BaseWitness; LongReservoir.base_witness applies this implication to its constructions."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-shiftpencilblocks-rectextend"),
                DeclarationHandle.Create(Owner + ".rectExtend"),
                H("rectExtend"), StatementSource.FromAuthor(Disp(Statement2())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("rectExtend extends a finite rectangular array by zero to natural-number coordinates; pencil_mulVec uses it to express the pencil recurrence uniformly at the boundary."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gls-shiftpencilblocks-shift1"),
                DeclarationHandle.Create(Owner + ".shift1"),
                H("shift1"), StatementSource.FromAuthor(Disp(Statement3())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("shift1 has entry one when the column index is one greater than the row index and zero elsewhere; pencil combines it with the rectangular identity to couple adjacent coordinates."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gls-shiftpencilblocks-pencil"),
                DeclarationHandle.Create(Owner + ".pencil"),
                H("pencil"), StatementSource.FromAuthor(Disp(Statement4())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("pencil is the sum of the unshifted and shifted Kronecker terms, mapping (x+1)*y input coordinates to x*(y+1) output coordinates; pencil_rank_of_le proves full row rank when x ≤ y."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gls-shiftpencilblocks-pencil-rank-of-le"),
                DeclarationHandle.Create(Owner + ".pencil_rank_of_le"),
                H("pencil_rank_of_le"), StatementSource.FromAuthor(Disp(Statement5())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When x ≤ y, pencil has full row rank x*(y+1), because its transpose recurrence propagates to a zero boundary. widthTwo_rank_of_lt applies this blockwise to dimension pairs with increasing depths."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-shiftpencilblocks-block-mulvec"),
                DeclarationHandle.Create(Owner + ".block_mulVec"),
                H("block_mulVec"), StatementSource.FromAuthor(Disp(Statement6())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Multiplication by a block-diagonal matrix acts on each block using only the corresponding input coordinates; blockKernelEquiv uses this identity to identify its kernel with the product of the individual kernels."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-shiftpencilblocks-tensorblockequiv"),
                DeclarationHandle.Create(Owner + ".tensorBlockEquiv"),
                H("tensorBlockEquiv"), StatementSource.FromAuthor(Disp(Statement7())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("tensorBlockEquiv groups a pair of dependent block indices into a single index for the pair of blocks; widthTwo_block_decomposition uses this reindexing to express the tensor matrix as a block-diagonal family of pencils."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gls-shiftpencilblocks-pencil-mulvec"),
                DeclarationHandle.Create(Owner + ".pencil_mulVec"),
                H("pencil_mulVec"), StatementSource.FromAuthor(Disp(Statement8())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At each output position, pencil multiplication adds the current input coordinate and the adjacent shifted coordinate, with zero extension at the boundary; antiDiagonal_kernel uses this recurrence to cancel successive alternating signs."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-shiftpencilblocks-antidiagonal"),
                DeclarationHandle.Create(Owner + ".antiDiagonal"),
                H("antiDiagonal"), StatementSource.FromAuthor(Disp(Statement9())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("antiDiagonal is supported where the two coordinate indices sum to p and has alternating signs there; antiDiagonal_kernel shows that it lies in the kernel of the short-long pencil."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gls-shiftpencilblocks-antidiagonal-kernel"),
                DeclarationHandle.Create(Owner + ".antiDiagonal_kernel"),
                H("antiDiagonal_kernel"), StatementSource.FromAuthor(Disp(Statement10())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The alternating anti-diagonal vector is annihilated by pencil p (p+1); ReservoirSchur.widthTwo_kernelEmbedding applies this in every short-long block to construct kernel vectors."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-shiftpencilblocks-blocklength"),
                DeclarationHandle.Create(Owner + ".blockLength"),
                H("blockLength"), StatementSource.FromAuthor(Disp(Statement11())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("blockLength assigns length p to each of the alpha short blocks and p+1 to each of the beta long blocks; arrow0 and arrow1 use these lengths to form their block-diagonal matrices."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gls-shiftpencilblocks-leftdim"),
                DeclarationHandle.Create(Owner + ".leftDim"),
                H("leftDim"), StatementSource.FromAuthor(Disp(Statement12())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("leftDim is the total row dimension p*alpha+(p+1)*beta of the shift blocks; rows_card identifies it with the cardinality of the dependent row-index type."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gls-shiftpencilblocks-rightdim"),
                DeclarationHandle.Create(Owner + ".rightDim"),
                H("rightDim"), StatementSource.FromAuthor(Disp(Statement13())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("rightDim is the total column dimension (p+1)*alpha+(p+2)*beta of the shift blocks; cols_card identifies it with the cardinality of the dependent column-index type."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gls-shiftpencilblocks-rows-card"),
                DeclarationHandle.Create(Owner + ".rows_card"),
                H("rows_card"), StatementSource.FromAuthor(Disp(Statement14())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The dependent row-index type has cardinality leftDim; same_depth_kernel_dimension uses this count with the rank calculation to compute the kernel dimension."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-shiftpencilblocks-cols-card"),
                DeclarationHandle.Create(Owner + ".cols_card"),
                H("cols_card"), StatementSource.FromAuthor(Disp(Statement15())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The dependent column-index type has cardinality rightDim; same_depth_kernel_dimension uses this count as the domain dimension in rank-nullity."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-shiftpencilblocks-arrow0"),
                DeclarationHandle.Create(Owner + ".arrow0"),
                H("arrow0"), StatementSource.FromAuthor(Disp(Statement16())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("arrow0 is the block-diagonal sum of the rectangular identity maps for the short and long blocks; widthTwoMatrix pairs it with the transpose of the second dimension pair’s unshifted map."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gls-shiftpencilblocks-arrow1"),
                DeclarationHandle.Create(Owner + ".arrow1"),
                H("arrow1"), StatementSource.FromAuthor(Disp(Statement17())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("arrow1 is the block-diagonal sum of the one-step shift maps for the short and long blocks; widthTwoMatrix pairs it with the transpose of the second dimension pair’s shifted map."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gls-shiftpencilblocks-widthtwomatrix"),
                DeclarationHandle.Create(Owner + ".widthTwoMatrix"),
                H("widthTwoMatrix"), StatementSource.FromAuthor(Disp(Statement18())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("widthTwoMatrix is the sum of the two Kronecker products formed from arrow0 and arrow1; widthTwo_block_decomposition splits it into rectangular pencils indexed by pairs of blocks."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gls-shiftpencilblocks-widthtwo-block-decomposition"),
                DeclarationHandle.Create(Owner + ".widthTwo_block_decomposition"),
                H("widthTwo_block_decomposition"), StatementSource.FromAuthor(Disp(Statement19())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reindexing the rows and columns identifies widthTwoMatrix with a block-diagonal family of rectangular pencils; widthTwo_rank_sum uses this decomposition to add their ranks."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-shiftpencilblocks-witness-of-typed-slices"),
                DeclarationHandle.Create(Owner + ".witness_of_typed_slices"),
                H("witness_of_typed_slices"), StatementSource.FromAuthor(Disp(Statement20())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A rational three-slice contraction attaining the smaller outer cut on arbitrary finite index types can be reindexed to Fin a, Fin b, Fin c and Fin d without changing rank; witness_of_widthTwo_rank applies this to the block-indexed construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-shiftpencilblocks-different-depth-witness"),
                DeclarationHandle.Create(Owner + ".different_depth_witness"),
                H("different_depth_witness"), StatementSource.FromAuthor(Disp(Statement21())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When the two depths differ, the width-two pencil already gives rational matrices attaining min(a*d,b*c) for the parameterized dimensions; LongReservoir.parameterized_base_witness uses this for the unequal-depth case."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-shiftpencilblocks-same-depth-kernel-dimension"),
                DeclarationHandle.Create(Owner + ".same_depth_kernel_dimension"),
                H("same_depth_kernel_dimension"), StatementSource.FromAuthor(Disp(Statement22())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At equal depths, the kernel of widthTwoMatrix has dimension alpha*delta; ReservoirSchur.kernelEmbedding_range combines this count with its injective kernel parametrization to show that every kernel vector has those coordinates."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-shiftpencilblocks-zero-defect-witness"),
                DeclarationHandle.Create(Owner + ".zero_defect_witness"),
                H("zero_defect_witness"), StatementSource.FromAuthor(Disp(Statement23())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At equal depths, if alpha*delta or beta*gamma vanishes, the width-two matrix attains the smaller outer cut; LongReservoir.parameterized_base_witness uses this for the zero-defect cases."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-shiftpencilblocks-double-fin-pick"),
                DeclarationHandle.Create(Owner + ".double_fin_pick"),
                H("double_fin_pick"), StatementSource.FromAuthor(Disp(Statement24())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A double finite sum supported at a single pair of indices equals the product of the two coefficients times the zero-extended array value; ReservoirSchur.reservoirCross_SL_short_row uses this to compute the added slice at a short-row position."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-shiftpencilblocks-neg-one-pow-square"),
                DeclarationHandle.Create(Owner + ".neg_one_pow_square"),
                H("neg_one_pow_square"), StatementSource.FromAuthor(Disp(Statement25())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The square of every integer power of -1 is one; ReservoirSchur.cokernel_reservoir_kernel uses this identity to cancel the two anti-diagonal signs in the projected reservoir equation."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-shiftpencilblocks-short-short-cyclic-schur-rank"),
                DeclarationHandle.Create(Owner + ".short_short_cyclic_schur_rank"),
                H("short_short_cyclic_schur_rank"), StatementSource.FromAuthor(Disp(Statement26())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For 0 < B ≤ A, 0 < D ≤ G and p > 0, the short reservoir Schur complement has rank min(A*D,B*G); ReservoirSchur.short_short_injective_witness combines this with the relevant dimension ordering to obtain an injective Schur map."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-shiftpencilblocks-long-long-cyclic-schur-rank"),
                DeclarationHandle.Create(Owner + ".long_long_cyclic_schur_rank"),
                H("long_long_cyclic_schur_rank"), StatementSource.FromAuthor(Disp(Statement27())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For 0 < A ≤ B, 0 < G ≤ D and p > 0, the long reservoir Schur complement has rank min(A*D,B*G); LongReservoir.long_long_injective_witness uses this rank to eliminate the remaining kernel coordinates."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-shiftpencilblocks-matrix-injective-of-rank"),
                DeclarationHandle.Create(Owner + ".matrix_injective_of_rank"),
                H("matrix_injective_of_rank"), StatementSource.FromAuthor(Disp(Statement28())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A rational matrix whose rank equals its number of columns defines an injective linear map; LongReservoir.long_long_injective_witness applies this to its full-column-rank Schur complement."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-shiftpencilblocks-schur-two-equations"),
                DeclarationHandle.Create(Owner + ".schur_two_equations"),
                H("schur_two_equations"), StatementSource.FromAuthor(Disp(Statement29())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If R is invertible and H-L*R⁻¹*T is injective, the two displayed coupled homogeneous equations imply v=w=0; ReservoirSchur.short_reservoir_injective and LongReservoir.long_reservoir_injective use this to prove injectivity of the augmented flow matrices."))),
                DescribeRole.Theorem))));

    private static Formula Statement0() =>
        Seq(Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("ParameterizedBaseWitness")), Sp, Iff, Sp,
        Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("p"), Sp, F.Id("q"), Sp, F.Id("alpha"), Sp, F.Id("beta"),
        Sp, F.Id("gamma"), Sp, F.Id("delta"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, D(0), Sp,
        F.Lt, Sp, F.Id("p"), Sp, To, Sp, D(0), Sp, F.Lt, Sp, F.Id("q"), Sp, To, Sp, D(0), Sp, F.Lt, Sp, F.Id("beta"),
        Sp, To, Sp, D(0), Sp, F.Lt, Sp, F.Id("delta"), Sp, To, Sp, Qualified(F.Id("QuantumMaxFlowBound"), Dot,
        F.Id("RationalWitness")), Sp, Parenthesized(Seq(F.Id("p"), Sp, Cdot, Sp, F.Id("alpha"), Sp, Plus, Sp,
        Parenthesized(Seq(F.Id("p"), Sp, Plus, Sp, D(1))), Sp, Cdot, Sp, F.Id("beta"))), Sp,
        Parenthesized(Seq(Parenthesized(Seq(F.Id("p"), Sp, Plus, Sp, D(1))), Sp, Cdot, Sp, F.Id("alpha"), Sp, Plus,
        Sp, Parenthesized(Seq(F.Id("p"), Sp, Plus, Sp, D(2))), Sp, Cdot, Sp, F.Id("beta"))), Sp,
        Parenthesized(Seq(F.Id("q"), Sp, Cdot, Sp, F.Id("gamma"), Sp, Plus, Sp, Parenthesized(Seq(F.Id("q"), Sp, Plus,
        Sp, D(1))), Sp, Cdot, Sp, F.Id("delta"))), Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("q"), Sp, Plus, Sp,
        D(1))), Sp, Cdot, Sp, F.Id("gamma"), Sp, Plus, Sp, Parenthesized(Seq(F.Id("q"), Sp, Plus, Sp, D(2))), Sp,
        Cdot, Sp, F.Id("delta"))))));

    private static Formula Statement1() =>
        Seq(Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("ParameterizedBaseWitness")), Sp, To, Sp,
        Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("BaseWitness")));

    private static Formula Statement2() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("x"), Sp, F.Id("y"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp,
        Parenthesized(Seq(F.Id("z"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("x"), Sp, Times, Sp, F.Id("Fin"), Sp,
        F.Id("y"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Parenthesized(Seq(F.Id("i"), Sp, F.Id("k"), Sp,
        Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Qualified(F.Id("ShiftPencilBlocks"), Dot,
        F.Id("rectExtend")), Sp, F.Id("z"), Sp, F.Id("i"), Sp, F.Id("k"), Sp, Eq, Sp, Parenthesized(Seq(F.Id("if"),
        Sp, F.Id("hi"), Sp, Colon, Sp, F.Id("i"), Sp, F.Lt, Sp, F.Id("x"), Sp, F.Id("then"), Sp, F.Id("if"), Sp,
        F.Id("hk"), Sp, Colon, Sp, F.Id("k"), Sp, F.Lt, Sp, F.Id("y"), Sp, F.Id("then"), Sp, F.Id("z"), Sp,
        Parenthesized(Seq(Seq(Langle, Sp, Seq(F.Id("i"), Sp, Comma, Sp, F.Id("hi")), Sp, Rangle), Sp, Comma, Sp,
        Seq(Langle, Sp, Seq(F.Id("k"), Sp, Comma, Sp, F.Id("hk")), Sp, Rangle))), Sp, F.Id("else"), Sp, D(0), Sp,
        F.Id("else"), Sp, D(0))));

    private static Formula Statement3() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp,
        Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("shift1")), Sp, F.Id("x"), Sp, Eq, Sp,
        Parenthesized(Seq(Qualified(F.Id("Matrix"), Dot, F.Id("submatrix")), Sp, D(1), Sp,
        Parenthesized(Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("x"))),
        Sp, Mapsto, Sp, Parenthesized(Call("val", F.Id("i"))), Sp, Plus, Sp, D(1))),
        Sp, Qualified(F.Id("Fin"), Dot, F.Id("val")))));

    private static Formula Statement4() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("x"), Sp, F.Id("y"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp,
        Comma, Sp, Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("pencil")), Sp, F.Id("x"), Sp, F.Id("y"), Sp, Eq,
        Sp, Parenthesized(Seq(Parenthesized(Seq(Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("rectId")), Sp,
        F.Id("x"), Sp, Parenthesized(Seq(F.Id("x"), Sp, Plus, Sp, D(1))))), Sp, Dot, Sp, F.Id("kronecker"), Sp,
        Parenthesized(Seq(Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("rectId")), Sp, F.Id("y"), Sp,
        Parenthesized(Seq(F.Id("y"), Sp, Plus, Sp, D(1))))), Sp, Dot, Sp, F.Id("transpose"), Sp, Plus, Sp,
        Parenthesized(Seq(Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("shift1")), Sp, F.Id("x"))), Sp, Dot, Sp,
        F.Id("kronecker"), Sp, Parenthesized(Seq(Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("shift1")), Sp,
        F.Id("y"))), Sp, Dot, Sp, F.Id("transpose"))));

    private static Formula Statement5() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("x"), Sp, F.Id("y"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp,
        Comma, Sp, F.Id("x"), Sp, Leq, Sp, F.Id("y"), Sp, To, Sp,
        Parenthesized(Seq(Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("pencil")), Sp, F.Id("x"), Sp, F.Id("y"))),
        Sp, Dot, Sp, F.Id("rank"), Sp, Eq, Sp, F.Id("x"), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("y"), Sp, Plus, Sp,
        D(1))));

    private static Formula Statement6() =>
        Seq(Forall, Sp, Seq(OpenBrace, Seq(Iota, Sp, Colon, Sp, F.Id("Type")), CloseBrace), Sp, Seq(OpenBracket,
        Seq(F.Id("Fintype"), Sp, Iota), CloseBracket), Sp, Seq(OpenBracket, Seq(F.Id("DecidableEq"), Sp, Iota),
        CloseBracket), Sp, Seq(OpenBrace, Seq(F.Id("m"), Sp, Colon, Sp, Iota, Sp, To, Sp, F.Id("Type")), CloseBrace),
        Sp, Seq(OpenBrace, Seq(F.Id("n"), Sp, Colon, Sp, Iota, Sp, To, Sp, F.Id("Type")), CloseBrace), Sp,
        Seq(OpenBracket, Seq(Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, Iota)), Sp, To, Sp, F.Id("Fintype"), Sp,
        Parenthesized(Seq(F.Id("m"), Sp, F.Id("i")))), CloseBracket), Sp, Seq(OpenBracket,
        Seq(Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, Iota)), Sp, To, Sp, F.Id("Fintype"), Sp,
        Parenthesized(Seq(F.Id("n"), Sp, F.Id("i")))), CloseBracket), Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp,
        Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, Iota)), Sp, To, Sp, F.Id("Matrix"), Sp,
        Parenthesized(Seq(F.Id("m"), Sp, F.Id("i"))), Sp, Parenthesized(Seq(F.Id("n"), Sp, F.Id("i"))), Sp,
        Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Parenthesized(Seq(F.Id("z"), Sp, Colon, Sp, Parenthesized(Seq(new
        Formula.Subscript(Sigma, Seq(F.Id("i"), Sp, Colon, Sp, Iota)), Sp, F.Id("n"), Sp, F.Id("i"))), Sp, To, Sp,
        Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, Iota)), Sp,
        Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, F.Id("m"), Sp, F.Id("i"))), Sp, Comma, Sp,
        Parenthesized(Seq(Qualified(F.Id("Matrix"), Dot, F.Id("blockDiagonal")), Sp, Apos, Sp, F.Id("A"))), Sp, Dot,
        Sp, F.Id("mulVec"), Sp, F.Id("z"), Sp, Seq(Langle, Sp, Seq(F.Id("i"), Sp, Comma, Sp, F.Id("j")), Sp, Rangle),
        Sp, Eq, Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("i"))), Sp, Dot, Sp, F.Id("mulVec"), Sp,
        Parenthesized(Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, F.Id("n"), Sp, F.Id("i"))), Sp,
        Mapsto, Sp, F.Id("z"), Sp, Seq(Langle, Sp, Seq(F.Id("i"), Sp, Comma, Sp, F.Id("k")), Sp, Rangle))), Sp,
        F.Id("j"));

    private static Formula Statement7() =>
        Seq(Forall, Sp, Parenthesized(Seq(Iota, Sp, Colon, Sp, F.Id("Type"))), Sp, Parenthesized(Seq(Kappa, Sp, Colon,
        Sp, F.Id("Type"))), Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Iota, Sp, To, Sp, F.Id("Type"))), Sp,
        Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Kappa, Sp, To, Sp, F.Id("Type"))), Sp, Comma, Sp,
        Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("tensorBlockEquiv")), Sp, F.Id("m"), Sp, F.Id("n"), Sp, Eq, Sp,
        Parenthesized(Seq(Parenthesized(Seq(Qualified(F.Id("Equiv"), Dot, F.Id("sigmaProdDistrib")), Sp, F.Id("m"),
        Sp, Parenthesized(Seq(new Formula.Subscript(Sigma, Seq(F.Id("j"), Sp, Colon, Sp, Kappa)), Sp, F.Id("n"), Sp,
        F.Id("j"))))), Sp, Dot, Sp, F.Id("trans"), Sp, Parenthesized(Seq(Parenthesized(Seq(Qualified(F.Id("Equiv"),
        Dot, F.Id("sigmaCongrRight")), Sp, F.Id("fun"), Sp, Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, Iota)), Sp,
        Mapsto, Sp, Parenthesized(Seq(Qualified(F.Id("Equiv"), Dot, F.Id("prodComm")), Sp,
        Parenthesized(Seq(F.Id("m"), Sp, F.Id("i"))), Sp, Parenthesized(Seq(new Formula.Subscript(Sigma,
        Seq(F.Id("j"), Sp, Colon, Sp, Kappa)), Sp, F.Id("n"), Sp, F.Id("j"))))), Sp, Dot, Sp, F.Id("trans"), Sp,
        Parenthesized(Seq(Parenthesized(Seq(Qualified(F.Id("Equiv"), Dot, F.Id("sigmaProdDistrib")), Sp, F.Id("n"),
        Sp, Parenthesized(Seq(F.Id("m"), Sp, F.Id("i"))))), Sp, Dot, Sp, F.Id("trans"), Sp,
        Parenthesized(Seq(Qualified(F.Id("Equiv"), Dot, F.Id("sigmaCongrRight")), Sp, F.Id("fun"), Sp,
        Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Kappa)), Sp, Mapsto, Sp, Qualified(F.Id("Equiv"), Dot,
        F.Id("prodComm")), Sp, Parenthesized(Seq(F.Id("n"), Sp, F.Id("j"))), Sp, Parenthesized(Seq(F.Id("m"), Sp,
        F.Id("i"))))))))), Sp, Dot, Sp, F.Id("trans"), Sp, Qualified(F.Id("Equiv"), Dot, F.Id("sigmaAssocProd"), Dot,
        F.Id("symm")))))));

    private static Formula Statement8() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("x"), Sp, F.Id("y"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp,
        Parenthesized(Seq(F.Id("u"), Sp, Colon, Sp, F.Id("Fin"), Sp, Parenthesized(Seq(F.Id("x"), Sp, Plus, Sp,
        D(1))), Sp, Times, Sp, F.Id("Fin"), Sp, F.Id("y"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp,
        Parenthesized(Seq(F.Id("r"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("x"), Sp, Times, Sp, F.Id("Fin"), Sp,
        Parenthesized(Seq(F.Id("y"), Sp, Plus, Sp, D(1))))), Sp, Comma, Sp,
        Parenthesized(Seq(Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("pencil")), Sp, F.Id("x"), Sp, F.Id("y"))),
        Sp, Dot, Sp, F.Id("mulVec"), Sp, F.Id("u"), Sp, F.Id("r"), Sp, Eq, Sp, Qualified(F.Id("ShiftPencilBlocks"),
        Dot, F.Id("rectExtend")), Sp, F.Id("u"), Sp, Parenthesized(Call("val", Seq(F.Id("r"), Sp, Dot, Sp, D(1)))), Sp, Parenthesized(Call("val", Seq(F.Id("r"), Sp, Dot, Sp, D(2)))), Sp, Plus, Sp, F.Id("if"), Sp, D(0), Sp, F.Lt, Sp, Parenthesized(Call("val", Seq(F.Id("r"), Sp, Dot, Sp, D(2)))), Sp, F.Id("then"), Sp,
        Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("rectExtend")), Sp, F.Id("u"), Sp,
        Parenthesized(Seq(Parenthesized(Call("val", Seq(F.Id("r"), Sp, Dot, Sp,
        D(1)))), Sp, Plus, Sp, D(1))), Sp, Parenthesized(Seq(Parenthesized(Call("val", Seq(F.Id("r"), Sp, Dot, Sp, D(2)))), Sp, Minus, Sp, D(1))), Sp, F.Id("else"), Sp, D(0));

    private static Formula Statement9() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("p"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp,
        Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, F.Id("Fin"), Sp, Parenthesized(Seq(F.Id("p"), Sp, Plus, Sp,
        D(1))), Sp, Times, Sp, F.Id("Fin"), Sp, Parenthesized(Seq(F.Id("p"), Sp, Plus, Sp, D(1))))), Sp, Comma, Sp,
        Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("antiDiagonal")), Sp, F.Id("p"), Sp, F.Id("k"), Sp, Eq, Sp,
        Parenthesized(Seq(F.Id("if"), Sp, Parenthesized(Call("val", Seq(F.Id("k"), Sp,
        Dot, Sp, D(1)))), Sp, Plus, Sp, Parenthesized(Call("val", Seq(F.Id("k"), Sp,
        Dot, Sp, D(2)))), Sp, Eq, Sp, F.Id("p"), Sp, F.Id("then"), Sp, new Formula.Power(Parenthesized(Seq(Minus, Sp,
        D(1))), Call("val", Seq(F.Id("k"), Sp, Dot, Sp, D(1)))), Sp, F.Id("else"),
        Sp, D(0))));

    private static Formula Statement10() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("p"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp,
        Parenthesized(Seq(Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("pencil")), Sp, F.Id("p"), Sp,
        Parenthesized(Seq(F.Id("p"), Sp, Plus, Sp, D(1))))), Sp, Dot, Sp, F.Id("mulVec"), Sp,
        Parenthesized(Seq(Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("antiDiagonal")), Sp, F.Id("p"))), Sp, Eq,
        Sp, D(0));

    private static Formula Statement11() =>
        Seq(Forall, Sp,
            Parenthesized(Seq(F.Id("p"), Sp, F.Id("alpha"), Sp, F.Id("beta"), Sp, Colon, Sp,
                Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp,
            Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("blockLength")), Sp,
            F.Id("p"), Sp, F.Id("alpha"), Sp, F.Id("beta"), Sp, Eq, Sp,
            Qualified(F.Id("Sum"), Dot, F.Id("elim")), Sp,
            Parenthesized(Seq(F.Id("fun"), Sp, Underscore, Sp, Mapsto, Sp, F.Id("p"))), Sp,
            Parenthesized(Seq(F.Id("fun"), Sp, Underscore, Sp, Mapsto, Sp, F.Id("p"), Sp, Plus, Sp, D(1))));

    private static Formula Statement12() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("p"), Sp, F.Id("alpha"), Sp, F.Id("beta"), Sp, Colon, Sp, Seq(Mathbb,
        Grp(F.Id("N"))))), Sp, Comma, Sp, Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("leftDim")), Sp, F.Id("p"),
        Sp, F.Id("alpha"), Sp, F.Id("beta"), Sp, Eq, Sp, Parenthesized(Seq(F.Id("p"), Sp, Cdot, Sp, F.Id("alpha"), Sp,
        Plus, Sp, Parenthesized(Seq(F.Id("p"), Sp, Plus, Sp, D(1))), Sp, Cdot, Sp, F.Id("beta"))));

    private static Formula Statement13() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("p"), Sp, F.Id("alpha"), Sp, F.Id("beta"), Sp, Colon, Sp, Seq(Mathbb,
        Grp(F.Id("N"))))), Sp, Comma, Sp, Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("rightDim")), Sp, F.Id("p"),
        Sp, F.Id("alpha"), Sp, F.Id("beta"), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("p"), Sp, Plus, Sp,
        D(1))), Sp, Cdot, Sp, F.Id("alpha"), Sp, Plus, Sp, Parenthesized(Seq(F.Id("p"), Sp, Plus, Sp, D(2))), Sp,
        Cdot, Sp, F.Id("beta"))));

    private static Formula Statement14() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("p"), Sp, F.Id("alpha"), Sp, F.Id("beta"), Sp, Colon, Sp, Seq(Mathbb,
        Grp(F.Id("N"))))), Sp, Comma, Sp, Qualified(F.Id("Fintype"), Dot, F.Id("card")), Sp,
        Parenthesized(Parenthesized(Seq(new Formula.Subscript(Sigma, Seq(F.Id("t"), Sp, Colon, Sp, F.Id("Sum"), Sp,
        Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("alpha"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("beta"))))),
        Sp, F.Id("Fin"), Sp, Parenthesized(Seq(Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("blockLength")), Sp,
        F.Id("p"), Sp, F.Id("alpha"), Sp, F.Id("beta"), Sp, F.Id("t")))))), Sp, Eq, Sp,
        Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("leftDim")), Sp, F.Id("p"), Sp, F.Id("alpha"), Sp,
        F.Id("beta"));

    private static Formula Statement15() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("p"), Sp, F.Id("alpha"), Sp, F.Id("beta"), Sp, Colon, Sp, Seq(Mathbb,
        Grp(F.Id("N"))))), Sp, Comma, Sp, Qualified(F.Id("Fintype"), Dot, F.Id("card")), Sp,
        Parenthesized(Parenthesized(Seq(new Formula.Subscript(Sigma, Seq(F.Id("t"), Sp, Colon, Sp, F.Id("Sum"), Sp,
        Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("alpha"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("beta"))))),
        Sp, F.Id("Fin"), Sp, Parenthesized(Seq(Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("blockLength")), Sp,
        F.Id("p"), Sp, F.Id("alpha"), Sp, F.Id("beta"), Sp, F.Id("t"), Sp, Plus, Sp, D(1)))))), Sp, Eq, Sp,
        Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("rightDim")), Sp, F.Id("p"), Sp, F.Id("alpha"), Sp,
        F.Id("beta"));

    private static Formula Statement16() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("p"), Sp, F.Id("alpha"), Sp, F.Id("beta"), Sp, Colon, Sp, Seq(Mathbb,
        Grp(F.Id("N"))))), Sp, Comma, Sp, Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("arrow0")), Sp, F.Id("p"),
        Sp, F.Id("alpha"), Sp, F.Id("beta"), Sp, Eq, Sp, Parenthesized(Seq(Qualified(F.Id("Matrix"), Dot,
        F.Id("blockDiagonal")), Sp, Apos, Sp, F.Id("fun"), Sp, Parenthesized(Seq(F.Id("t"), Sp, Colon, Sp,
        F.Id("Sum"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("alpha"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp,
        F.Id("beta"))))), Sp, Mapsto, Sp, Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("rectId")), Sp,
        Parenthesized(Seq(Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("blockLength")), Sp, F.Id("p"), Sp,
        F.Id("alpha"), Sp, F.Id("beta"), Sp, F.Id("t"))), Sp, Parenthesized(Seq(Qualified(F.Id("ShiftPencilBlocks"),
        Dot, F.Id("blockLength")), Sp, F.Id("p"), Sp, F.Id("alpha"), Sp, F.Id("beta"), Sp, F.Id("t"), Sp, Plus, Sp,
        D(1))))));

    private static Formula Statement17() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("p"), Sp, F.Id("alpha"), Sp, F.Id("beta"), Sp, Colon, Sp, Seq(Mathbb,
        Grp(F.Id("N"))))), Sp, Comma, Sp, Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("arrow1")), Sp, F.Id("p"),
        Sp, F.Id("alpha"), Sp, F.Id("beta"), Sp, Eq, Sp, Parenthesized(Seq(Qualified(F.Id("Matrix"), Dot,
        F.Id("blockDiagonal")), Sp, Apos, Sp, F.Id("fun"), Sp, Parenthesized(Seq(F.Id("t"), Sp, Colon, Sp,
        F.Id("Sum"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("alpha"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp,
        F.Id("beta"))))), Sp, Mapsto, Sp, Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("shift1")), Sp,
        Parenthesized(Seq(Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("blockLength")), Sp, F.Id("p"), Sp,
        F.Id("alpha"), Sp, F.Id("beta"), Sp, F.Id("t"))))));

    private static Formula Statement18() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("p"), Sp, F.Id("q"), Sp, F.Id("alpha"), Sp, F.Id("beta"), Sp,
        F.Id("gamma"), Sp, F.Id("delta"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp,
        Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("widthTwoMatrix")), Sp, F.Id("p"), Sp, F.Id("q"), Sp,
        F.Id("alpha"), Sp, F.Id("beta"), Sp, F.Id("gamma"), Sp, F.Id("delta"), Sp, Eq, Sp,
        Parenthesized(Seq(Parenthesized(Seq(Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("arrow0")), Sp, F.Id("p"),
        Sp, F.Id("alpha"), Sp, F.Id("beta"))), Sp, Dot, Sp, F.Id("kronecker"), Sp,
        Parenthesized(Seq(Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("arrow0")), Sp, F.Id("q"), Sp, F.Id("gamma"),
        Sp, F.Id("delta"))), Sp, Dot, Sp, F.Id("transpose"), Sp, Plus, Sp,
        Parenthesized(Seq(Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("arrow1")), Sp, F.Id("p"), Sp, F.Id("alpha"),
        Sp, F.Id("beta"))), Sp, Dot, Sp, F.Id("kronecker"), Sp, Parenthesized(Seq(Qualified(F.Id("ShiftPencilBlocks"),
        Dot, F.Id("arrow1")), Sp, F.Id("q"), Sp, F.Id("gamma"), Sp, F.Id("delta"))), Sp, Dot, Sp,
        F.Id("transpose"))));

    private static Formula Statement19() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("p"), Sp, F.Id("q"), Sp, F.Id("alpha"), Sp, F.Id("beta"), Sp,
        F.Id("gamma"), Sp, F.Id("delta"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp,
        Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("widthTwoMatrix")), Sp, F.Id("p"), Sp, F.Id("q"), Sp,
        F.Id("alpha"), Sp, F.Id("beta"), Sp, F.Id("gamma"), Sp, F.Id("delta"), Sp, Eq, Sp,
        Parenthesized(Seq(Qualified(F.Id("Matrix"), Dot, F.Id("blockDiagonal")), Sp, Apos, Sp, F.Id("fun"), Sp,
        Parenthesized(Seq(F.Id("t"), Sp, Colon, Sp, Parenthesized(Seq(F.Id("Sum"), Sp, Parenthesized(Seq(F.Id("Fin"),
        Sp, F.Id("alpha"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("beta"))))), Sp, Times, Sp,
        Parenthesized(Seq(F.Id("Sum"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("gamma"))), Sp,
        Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("delta"))))))), Sp, Mapsto, Sp, Qualified(F.Id("ShiftPencilBlocks"),
        Dot, F.Id("pencil")), Sp, Parenthesized(Seq(Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("blockLength")),
        Sp, F.Id("p"), Sp, F.Id("alpha"), Sp, F.Id("beta"), Sp, F.Id("t"), Sp, Dot, Sp, D(1))), Sp,
        Parenthesized(Seq(Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("blockLength")), Sp, F.Id("q"), Sp,
        F.Id("gamma"), Sp, F.Id("delta"), Sp, F.Id("t"), Sp, Dot, Sp, D(2))))), Sp, Dot, Sp, F.Id("submatrix"), Sp,
        Parenthesized(new Formula.Apply(Qualified("CoeFun", "coe"), [Seq(Qualified(F.Id("ShiftPencilBlocks"), Dot,
        F.Id("tensorBlockEquiv")), Sp, Parenthesized(Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id("t"), Sp, Colon, Sp,
        F.Id("Sum"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("alpha"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp,
        F.Id("beta"))))), Sp, Mapsto, Sp, F.Id("Fin"), Sp, Parenthesized(Seq(Qualified(F.Id("ShiftPencilBlocks"), Dot,
        F.Id("blockLength")), Sp, F.Id("p"), Sp, F.Id("alpha"), Sp, F.Id("beta"), Sp, F.Id("t"))))), Sp, F.Id("fun"),
        Sp, Parenthesized(Seq(F.Id("t"), Sp, Colon, Sp, F.Id("Sum"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp,
        F.Id("gamma"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("delta"))))), Sp, Mapsto, Sp, F.Id("Fin"), Sp,
        Parenthesized(Seq(Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("blockLength")), Sp, F.Id("q"), Sp,
        F.Id("gamma"), Sp, F.Id("delta"), Sp, F.Id("t"), Sp, Plus, Sp, D(1))))])), Sp, Parenthesized(new
        Formula.Apply(Qualified("CoeFun", "coe"), [Seq(Qualified(F.Id("ShiftPencilBlocks"), Dot,
        F.Id("tensorBlockEquiv")), Sp, Parenthesized(Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id("t"), Sp, Colon, Sp,
        F.Id("Sum"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("alpha"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp,
        F.Id("beta"))))), Sp, Mapsto, Sp, F.Id("Fin"), Sp, Parenthesized(Seq(Qualified(F.Id("ShiftPencilBlocks"), Dot,
        F.Id("blockLength")), Sp, F.Id("p"), Sp, F.Id("alpha"), Sp, F.Id("beta"), Sp, F.Id("t"), Sp, Plus, Sp,
        D(1))))), Sp, F.Id("fun"), Sp, Parenthesized(Seq(F.Id("t"), Sp, Colon, Sp, F.Id("Sum"), Sp,
        Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("gamma"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("delta"))))),
        Sp, Mapsto, Sp, F.Id("Fin"), Sp, Parenthesized(Seq(Qualified(F.Id("ShiftPencilBlocks"), Dot,
        F.Id("blockLength")), Sp, F.Id("q"), Sp, F.Id("gamma"), Sp, F.Id("delta"), Sp, F.Id("t"))))])));

    private static Formula Statement20() =>
        Seq(Forall, Sp, Seq(OpenBrace, Seq(F.Id("I"), Sp, Colon, Sp, F.Id("Type")), CloseBrace), Sp, Seq(OpenBrace,
        Seq(F.Id("J"), Sp, Colon, Sp, F.Id("Type")), CloseBrace), Sp, Seq(OpenBrace, Seq(F.Id("K"), Sp, Colon, Sp,
        F.Id("Type")), CloseBrace), Sp, Seq(OpenBrace, Seq(F.Id("L"), Sp, Colon, Sp, F.Id("Type")), CloseBrace), Sp,
        Seq(OpenBracket, Seq(F.Id("Fintype"), Sp, F.Id("I")), CloseBracket), Sp, Seq(OpenBracket, Seq(F.Id("Fintype"),
        Sp, F.Id("J")), CloseBracket), Sp, Seq(OpenBracket, Seq(F.Id("Fintype"), Sp, F.Id("K")), CloseBracket), Sp,
        Seq(OpenBracket, Seq(F.Id("Fintype"), Sp, F.Id("L")), CloseBracket), Sp, Seq(OpenBrace, Seq(F.Id("a"), Sp,
        F.Id("b"), Sp, F.Id("c"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), CloseBrace), Sp, Comma,
        Sp, Qualified(F.Id("Fintype"), Dot, F.Id("card")), Sp, F.Id("I"), Sp, Eq, Sp, F.Id("a"), Sp, To, Sp,
        Qualified(F.Id("Fintype"), Dot, F.Id("card")), Sp, F.Id("J"), Sp, Eq, Sp, F.Id("b"), Sp, To, Sp,
        Qualified(F.Id("Fintype"), Dot, F.Id("card")), Sp, F.Id("K"), Sp, Eq, Sp, F.Id("c"), Sp, To, Sp,
        Qualified(F.Id("Fintype"), Dot, F.Id("card")), Sp, F.Id("L"), Sp, Eq, Sp, F.Id("d"), Sp, To, Sp, Forall, Sp,
        Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, F.Id("Fin"), Sp, D(3), Sp, To, Sp, F.Id("Matrix"), Sp, F.Id("I"),
        Sp, F.Id("J"), Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Parenthesized(Seq(F.Id("N"), Sp, Colon, Sp, F.Id("Fin"),
        Sp, D(3), Sp, To, Sp, F.Id("Matrix"), Sp, F.Id("L"), Sp, F.Id("K"), Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp,
        Comma, Sp, Parenthesized(Seq(new Formula.Subscript(Sum, Seq(F.Id("r"), Sp, Colon, Sp, F.Id("Fin"), Sp, D(3))),
        Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("M"), Sp, F.Id("r"))), Sp, Dot, Sp, F.Id("kronecker"), Sp,
        Parenthesized(Seq(F.Id("N"), Sp, F.Id("r"))))))), Sp, Dot, Sp, F.Id("rank"), Sp, Eq, Sp, F.Id("min"), Sp,
        Parenthesized(Seq(F.Id("a"), Sp, Cdot, Sp, F.Id("d"))), Sp, Parenthesized(Seq(F.Id("b"), Sp, Cdot, Sp,
        F.Id("c"))), Sp, To, Sp, Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("RationalWitness")), Sp, F.Id("a"),
        Sp, F.Id("b"), Sp, F.Id("c"), Sp, F.Id("d"));

    private static Formula Statement21() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("p"), Sp, F.Id("q"), Sp, F.Id("alpha"), Sp, F.Id("beta"), Sp,
        F.Id("gamma"), Sp, F.Id("delta"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, F.Id("p"), Sp,
        Neq, Sp, F.Id("q"), Sp, To, Sp, Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("RationalWitness")), Sp,
        Parenthesized(Seq(Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("leftDim")), Sp, F.Id("p"), Sp,
        F.Id("alpha"), Sp, F.Id("beta"))), Sp, Parenthesized(Seq(Qualified(F.Id("ShiftPencilBlocks"), Dot,
        F.Id("rightDim")), Sp, F.Id("p"), Sp, F.Id("alpha"), Sp, F.Id("beta"))), Sp,
        Parenthesized(Seq(Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("leftDim")), Sp, F.Id("q"), Sp,
        F.Id("gamma"), Sp, F.Id("delta"))), Sp, Parenthesized(Seq(Qualified(F.Id("ShiftPencilBlocks"), Dot,
        F.Id("rightDim")), Sp, F.Id("q"), Sp, F.Id("gamma"), Sp, F.Id("delta"))));

    private static Formula Statement22() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("p"), Sp, F.Id("alpha"), Sp, F.Id("beta"), Sp, F.Id("gamma"), Sp,
        F.Id("delta"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Qualified(F.Id("Module"), Dot,
        F.Id("finrank")), Sp, Seq(Mathbb, Grp(F.Id("Q"))), Sp, Parenthesized(new Formula.Apply(Qualified("CoeSort",
        "coe"), [Seq(Seq(Parenthesized(Seq(Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("widthTwoMatrix")), Sp,
        F.Id("p"), Sp, F.Id("p"), Sp, F.Id("alpha"), Sp, F.Id("beta"), Sp, F.Id("gamma"), Sp, F.Id("delta"))), Sp,
        Dot, Sp, F.Id("mulVecLin")), Sp, Dot, Sp, F.Id("ker"))])), Sp, Eq, Sp, F.Id("alpha"), Sp, Cdot, Sp,
        F.Id("delta"));

    private static Formula Statement23() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("p"), Sp, F.Id("alpha"), Sp, F.Id("beta"), Sp, F.Id("gamma"), Sp,
        F.Id("delta"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("alpha"), Sp, Cdot, Sp, F.Id("delta"), Sp, Eq, Sp, D(0), Sp,
            Lor, Sp, F.Id("beta"), Sp, Cdot, Sp, F.Id("gamma"), Sp, Eq, Sp, D(0))), Sp,
        To, Sp, Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("RationalWitness")), Sp,
        Parenthesized(Seq(Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("leftDim")), Sp, F.Id("p"), Sp,
        F.Id("alpha"), Sp, F.Id("beta"))), Sp, Parenthesized(Seq(Qualified(F.Id("ShiftPencilBlocks"), Dot,
        F.Id("rightDim")), Sp, F.Id("p"), Sp, F.Id("alpha"), Sp, F.Id("beta"))), Sp,
        Parenthesized(Seq(Qualified(F.Id("ShiftPencilBlocks"), Dot, F.Id("leftDim")), Sp, F.Id("p"), Sp,
        F.Id("gamma"), Sp, F.Id("delta"))), Sp, Parenthesized(Seq(Qualified(F.Id("ShiftPencilBlocks"), Dot,
        F.Id("rightDim")), Sp, F.Id("p"), Sp, F.Id("gamma"), Sp, F.Id("delta"))));

    private static Formula Statement24() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, F.Id("m"), Sp, F.Id("r"), Sp, F.Id("s"), Sp, Colon, Sp,
        Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("a"), Sp, F.Id("b"), Sp, Colon, Sp, Seq(Mathbb,
        Grp(F.Id("Q"))))), Sp, Parenthesized(Seq(F.Id("u"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"), Sp, Times, Sp,
        F.Id("Fin"), Sp, F.Id("m"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Comma, Sp, Seq(new
        Formula.Subscript(Sum, Seq(F.Id("i"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(new
        Formula.Subscript(Sum, Seq(F.Id("j"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("m"))), Sp,
        Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(F.Id("if"), Sp, Parenthesized(Call("val", F.Id("i"))), Sp, Eq, Sp, F.Id("r"), Sp, F.Id("then"), Sp, F.Id("a"),
        Sp, F.Id("else"), Sp, D(0))), Sp, Cdot, Sp, F.Id("if"), Sp, Parenthesized(Call("val", F.Id("j"))), Sp, Eq, Sp, F.Id("s"), Sp, F.Id("then"), Sp, F.Id("b"), Sp, F.Id("else"), Sp, D(0))),
        Sp, Cdot, Sp, F.Id("u"), Sp, Parenthesized(Seq(F.Id("i"), Sp, Comma, Sp, F.Id("j")))))))), Sp, Eq, Sp,
        F.Id("a"), Sp, Cdot, Sp, F.Id("b"), Sp, Cdot, Sp, Qualified(F.Id("ShiftPencilBlocks"), Dot,
        F.Id("rectExtend")), Sp, F.Id("u"), Sp, F.Id("r"), Sp, F.Id("s"));

    private static Formula Statement25() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, new
        Formula.Power(Parenthesized(Seq(Minus, Sp, D(1))), F.Id("n")), Sp, Cdot, Sp, new
        Formula.Power(Parenthesized(Seq(Minus, Sp, D(1))), F.Id("n")), Sp, Eq, Sp, D(1));

    private static Formula Statement26() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("B"), Sp, F.Id("G"), Sp, F.Id("D"), Sp, F.Id("p"), Sp,
        Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, D(0), Sp, F.Lt, Sp, F.Id("B"), Sp, To, Sp, F.Id("B"),
        Sp, Leq, Sp, F.Id("A"), Sp, To, Sp, D(0), Sp, F.Lt, Sp, F.Id("D"), Sp, To, Sp, F.Id("D"), Sp, Leq, Sp,
        F.Id("G"), Sp, To, Sp, D(0), Sp, F.Lt, Sp, F.Id("p"), Sp, To, Sp,
        Parenthesized(Seq(Parenthesized(Seq(Parenthesized(new Formula.Apply(Qualified("Coe", "coe"), [F.Id("p")])),
        Sp, Plus, Sp, D(1))), Sp, Cdot, Sp, Parenthesized(Seq(Qualified(F.Id("FloorSelectorCycles"), Dot,
        F.Id("rowSelector")), Sp, F.Id("A"), Sp, F.Id("B"))), Sp, Dot, Sp, F.Id("kronecker"), Sp,
        Parenthesized(Seq(Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("rowSelector")), Sp, F.Id("G"), Sp,
        F.Id("D"))), Sp, Dot, Sp, F.Id("transpose"), Sp, Minus, Sp,
        Parenthesized(Seq(Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("rowSelector")), Sp, F.Id("A"), Sp,
        F.Id("B"))), Sp, Dot, Sp, F.Id("kronecker"), Sp, Parenthesized(Seq(Qualified(F.Id("FloorSelectorCycles"), Dot,
        F.Id("forwardHalf")), Sp, F.Id("G"))), Sp, Cdot, Sp, new
        Formula.Power(Parenthesized(Seq(Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("reservoir")), Sp, F.Id("A"),
        Sp, F.Id("G"))), new Formula.Negate(D(1))), Sp, Cdot, Sp, Parenthesized(Seq(Minus, Sp,
        Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("backward")), Sp, F.Id("A"))), Sp, Dot, Sp,
        F.Id("kronecker"), Sp, Parenthesized(Seq(Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("rowSelector")), Sp,
        F.Id("G"), Sp, F.Id("D"))), Sp, Dot, Sp, F.Id("transpose"))), Sp, Dot, Sp, F.Id("rank"), Sp, Eq, Sp,
        F.Id("min"), Sp, Parenthesized(Seq(F.Id("A"), Sp, Cdot, Sp, F.Id("D"))), Sp, Parenthesized(Seq(F.Id("B"), Sp,
        Cdot, Sp, F.Id("G"))));

    private static Formula Statement27() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("B"), Sp, F.Id("G"), Sp, F.Id("D"), Sp, F.Id("p"), Sp,
        Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, D(0), Sp, F.Lt, Sp, F.Id("A"), Sp, To, Sp, F.Id("A"),
        Sp, Leq, Sp, F.Id("B"), Sp, To, Sp, D(0), Sp, F.Lt, Sp, F.Id("G"), Sp, To, Sp, F.Id("G"), Sp, Leq, Sp,
        F.Id("D"), Sp, To, Sp, D(0), Sp, F.Lt, Sp, F.Id("p"), Sp, To, Sp,
        Parenthesized(Seq(Parenthesized(Seq(Parenthesized(new Formula.Apply(Qualified("Coe", "coe"), [F.Id("p")])),
        Sp, Plus, Sp, D(1))), Sp, Cdot, Sp, Parenthesized(Seq(Qualified(F.Id("FloorSelectorCycles"), Dot,
        F.Id("rowSelector")), Sp, F.Id("B"), Sp, F.Id("A"))), Sp, Dot, Sp, Qualified(F.Id("transpose"), Dot,
        F.Id("kronecker")), Sp, Parenthesized(Seq(Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("rowSelector")),
        Sp, F.Id("D"), Sp, F.Id("G"))), Sp, Minus, Sp, Parenthesized(Seq(Minus, Sp,
        Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("backward")), Sp, F.Id("B"))), Sp, Dot, Sp,
        Qualified(F.Id("transpose"), Dot, F.Id("kronecker")), Sp,
        Parenthesized(Seq(Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("rowSelector")), Sp, F.Id("D"), Sp,
        F.Id("G"))), Sp, Cdot, Sp, new Formula.Power(Parenthesized(Seq(D(1), Sp, Plus, Sp, Parenthesized(Seq(Minus,
        Sp, Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("backward")), Sp, F.Id("B"))), Sp, Dot, Sp,
        Qualified(F.Id("transpose"), Dot, F.Id("kronecker")), Sp,
        Parenthesized(Seq(Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("forwardHalf")), Sp, F.Id("D"))), Sp, Dot,
        Sp, F.Id("transpose"))), new Formula.Negate(D(1))), Sp, Cdot, Sp,
        Parenthesized(Seq(Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("rowSelector")), Sp, F.Id("B"), Sp,
        F.Id("A"))), Sp, Dot, Sp, Qualified(F.Id("transpose"), Dot, F.Id("kronecker")), Sp,
        Parenthesized(Seq(Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("forwardHalf")), Sp, F.Id("D"))), Sp, Dot,
        Sp, F.Id("transpose"))), Sp, Dot, Sp, F.Id("rank"), Sp, Eq, Sp, F.Id("min"), Sp, Parenthesized(Seq(F.Id("A"),
        Sp, Cdot, Sp, F.Id("D"))), Sp, Parenthesized(Seq(F.Id("B"), Sp, Cdot, Sp, F.Id("G"))));

    private static Formula Statement28() =>
        Seq(Forall, Sp, Seq(OpenBrace, Seq(F.Id("m"), Sp, Colon, Sp, F.Id("Type")), CloseBrace), Sp, Seq(OpenBrace,
        Seq(F.Id("n"), Sp, Colon, Sp, F.Id("Type")), CloseBrace), Sp, Seq(OpenBracket, Seq(F.Id("Fintype"), Sp,
        F.Id("m")), CloseBracket), Sp, Seq(OpenBracket, Seq(F.Id("Fintype"), Sp, F.Id("n")), CloseBracket), Sp,
        Seq(OpenBracket, Seq(F.Id("DecidableEq"), Sp, F.Id("n")), CloseBracket), Sp, Parenthesized(Seq(F.Id("A"), Sp,
        Colon, Sp, F.Id("Matrix"), Sp, F.Id("m"), Sp, F.Id("n"), Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Comma, Sp,
        Qualified(F.Id("A"), Dot, F.Id("rank")), Sp, Eq, Sp, Qualified(F.Id("Fintype"), Dot, F.Id("card")), Sp,
        F.Id("n"), Sp, To, Sp, Qualified(F.Id("Function"), Dot, F.Id("Injective")), Sp, Parenthesized(new
        Formula.Apply(Qualified("CoeFun", "coe"), [Seq(F.Id("A"), Sp, Dot, Sp, F.Id("mulVecLin"))])));

    private static Formula Statement29() =>
        Seq(Forall, Sp, Seq(OpenBrace, Seq(F.Id("m"), Sp, Colon, Sp, F.Id("Type")), CloseBrace), Sp, Seq(OpenBrace,
        Seq(F.Id("n"), Sp, Colon, Sp, F.Id("Type")), CloseBrace), Sp, Seq(OpenBrace, Seq(F.Id("k"), Sp, Colon, Sp,
        F.Id("Type")), CloseBrace), Sp, Seq(OpenBracket, Seq(F.Id("Fintype"), Sp, F.Id("m")), CloseBracket), Sp,
        Seq(OpenBracket, Seq(F.Id("Fintype"), Sp, F.Id("n")), CloseBracket), Sp, Seq(OpenBracket, Seq(F.Id("Fintype"),
        Sp, F.Id("k")), CloseBracket), Sp, Seq(OpenBracket, Seq(F.Id("DecidableEq"), Sp, F.Id("m")), CloseBracket),
        Sp, Seq(OpenBracket, Seq(F.Id("DecidableEq"), Sp, F.Id("n")), CloseBracket), Sp, Seq(OpenBracket,
        Seq(F.Id("DecidableEq"), Sp, F.Id("k")), CloseBracket), Sp, Parenthesized(Seq(F.Id("R"), Sp, Colon, Sp,
        F.Id("Matrix"), Sp, F.Id("m"), Sp, F.Id("m"), Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp,
        Parenthesized(Seq(F.Id("T"), Sp, Colon, Sp, F.Id("Matrix"), Sp, F.Id("m"), Sp, F.Id("n"), Sp, Seq(Mathbb,
        Grp(F.Id("Q"))))), Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, F.Id("Matrix"), Sp, F.Id("k"), Sp,
        F.Id("m"), Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Parenthesized(Seq(F.Id("H"), Sp, Colon, Sp, F.Id("Matrix"),
        Sp, F.Id("k"), Sp, F.Id("n"), Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Comma, Sp, F.Id("IsUnit"), Sp, F.Id("R"),
        Sp, To, Sp, Qualified(F.Id("Function"), Dot, F.Id("Injective")), Sp, Parenthesized(Seq(F.Id("H"), Sp, Minus,
        Sp, F.Id("L"), Sp, Cdot, Sp, new Formula.Power(F.Id("R"), new Formula.Negate(D(1))), Sp, Cdot, Sp,
        F.Id("T"))), Sp, Dot, Sp, F.Id("mulVec"), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("v"), Sp, Colon, Sp,
        F.Id("m"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Parenthesized(Seq(F.Id("w"), Sp, Colon, Sp,
        F.Id("n"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Comma, Sp, Qualified(F.Id("R"), Dot,
        F.Id("mulVec")), Sp, F.Id("v"), Sp, Plus, Sp, Qualified(F.Id("T"), Dot, F.Id("mulVec")), Sp, F.Id("w"), Sp,
        Eq, Sp, D(0), Sp, To, Sp, Qualified(F.Id("L"), Dot, F.Id("mulVec")), Sp, F.Id("v"), Sp, Plus, Sp,
        Qualified(F.Id("H"), Dot, F.Id("mulVec")), Sp, F.Id("w"), Sp, Eq, Sp, D(0), Sp, To, Sp, F.Id("v"), Sp, Eq, Sp,
        D(0), Sp, Land, Sp, F.Id("w"), Sp, Eq, Sp, D(0));

}
