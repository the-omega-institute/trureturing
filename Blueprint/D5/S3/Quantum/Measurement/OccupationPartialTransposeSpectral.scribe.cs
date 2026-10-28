using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class OccupationPartialTransposeSpectralDocument : IScribeDocumentDefinition
{
    private static LibraryNoteRef Note => LibraryNoteRef.Create("D5/L/QuantumChannels/mista2006partialestimation");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal occupation operators and the exact qudit partial-estimation frontier.",
        H("OccupationPartialTransposeSpectral"), Blocks(
            Describe.Lean(DescribeId.Create("occupationpartialtransposespectral-blockdiagonal-psd"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.blockDiagonal_psd"),
                H("MatrixBlocks.blockDiagonal_psd"),
                StatementSource.FromAuthor(Disp(
                    All("s", Q("Type"), All("i", Q("Type"),
                        Instances(Id("s"), Instances(Id("i"),
                            All("B", Arrow(Id("s"), Q("Matrix", Id("i"), Id("i"), ComplexType)),
                                Implies(All("x", Id("s"), Q("Matrix.PosSemidef", App(Id("B"), Id("x")))),
                                    Q("Matrix.PosSemidef", Q("Matrix.blockDiagonal", Id("B"))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A block diagonal matrix is positive semidefinite whenever every block is positive semidefinite. The blocks and their common matrix indices range over arbitrary finite types."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("occupationpartialtransposespectral-occfintype"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.occFintype"),
                H("occFintype"), StatementSource.FromAuthor(Disp(All("N", NatType, All("d", NatType, Equal(Q("occFintype", Id("N"), Id("d")), Q("Fintype.ofEquiv", Q("Sym", Q("Fin", Id("d")), Id("N")), Q("Sym.equivNatSumOfFintype", Q("Fin", Id("d")), Id("N")))))))),
                AssessedProvenance.FromRepo(Note), Blocks(Paragraph(Text("The symmetric-power equivalence gives the finite occupation carrier."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("occupationpartialtransposespectral-symmetricprojector"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.symmetricProjector"),
                H("symmetricProjector"), StatementSource.FromAuthor(Disp(All("N", NatType, All("d", NatType, Equal(Q("symmetricProjector", Id("N"), Id("d")), SumAt("t", SubtypeOf("n", Arrow(Q("Fin", Id("d")), NatType), Equal(SumAt("i", Q("Fin", Id("d")), App(Id("n"), Id("i"))), Add(Id("N"), D(1)))), Q("Matrix.vecMulVec", Q("D5.S3.Quantum.Entanglement.OccupancyWordSectors.sectorVector", Add(Id("N"), D(1)), Q("val", Q("Equiv.symm", Q("Sym.equivNatSumOfFintype", Q("Fin", Id("d")), Add(Id("N"), D(1))), Id("t")))), Q("star", Q("D5.S3.Quantum.Entanglement.OccupancyWordSectors.sectorVector", Add(Id("N"), D(1)), Q("val", Q("Equiv.symm", Q("Sym.equivNatSumOfFintype", Q("Fin", Id("d")), Add(Id("N"), D(1))), Id("t")))))))))))),
                AssessedProvenance.FromLiterature(Note), Blocks(Paragraph(Text("Equation (14), p. 3, sums the projectors onto the normalized occupation vectors on the full word space."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("occupationpartialtransposespectral-occupationembedding"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.occupationEmbedding"),
                H("occupationEmbedding"), StatementSource.FromAuthor(Disp(All("N", NatType, All("d", NatType, All("w", Arrow(Q("Fin", Add(Id("N"), D(1))), Q("Fin", Id("d"))), All("x", Q("Prod", SubtypeOf("n", Arrow(Q("Fin", Id("d")), NatType), Equal(SumAt("i", Q("Fin", Id("d")), App(Id("n"), Id("i"))), Id("N"))), Q("Fin", Id("d"))), Equal(Q("occupationEmbedding", Id("N"), Id("d"), Id("w"), Id("x")), Mul(App(Q("D5.S3.Quantum.Entanglement.OccupancyWordSectors.sectorVector", Id("N"), Q("val", Q("Equiv.symm", Q("Sym.equivNatSumOfFintype", Q("Fin", Id("d")), Id("N")), Field(Id("x"), "1")))), Q("Fin.init", Id("w"))), IfThenElse(Equal(App(Id("w"), Q("Fin.last", Id("N"))), Field(Id("x"), "2")), D(1), D(0)))))))))),
                AssessedProvenance.FromRepo(Note), Blocks(Paragraph(Text("The occupation embedding sends an input occupation and output level to the normalized symmetric input vector times the output coordinate."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("occupationpartialtransposespectral-rf"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.RF"),
                H("RF"), StatementSource.FromAuthor(Disp(All("N", NatType, All("d", NatType, Equal(Q("RF", Id("N"), Id("d")), Scale(Q("Inv.inv", Typed(Q("Nat.choose", Sub(Add(Add(Id("N"), D(1)), Id("d")), D(1)), Sub(Id("d"), D(1))), ComplexType)), Mul(Mul(Q("Matrix.conjTranspose", Q("occupationEmbedding", Id("N"), Id("d"))), Q("Matrix.of", Lambda("u", Arrow(Q("Fin", Add(Id("N"), D(1))), Q("Fin", Id("d"))), Lambda("v", Arrow(Q("Fin", Add(Id("N"), D(1))), Q("Fin", Id("d"))), App(Q("symmetricProjector", Id("N"), Id("d")), Q("Fin.snoc", Q("Fin.init", Id("v")), App(Id("u"), Q("Fin.last", Id("N")))), Q("Fin.snoc", Q("Fin.init", Id("u")), App(Id("v"), Q("Fin.last", Id("N"))))))))), Q("occupationEmbedding", Id("N"), Id("d"))))))))),
                AssessedProvenance.FromLiterature(Note), Blocks(Paragraph(Text("RF is R_F of Eq. (12), p. 2: normalized compression of the partially transposed full symmetric projector."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("occupationpartialtransposespectral-outputreferenceprojector"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.outputReferenceProjector"),
                H("outputReferenceProjector"), StatementSource.FromAuthor(Disp(All("N", NatType, All("d", NatType, Equal(Q("outputReferenceProjector", Id("N"), Id("d")), Q("Matrix.kronecker", Typed(D(1), Q("Matrix", SubtypeOf("n", Arrow(Q("Fin", Id("d")), NatType), Equal(SumAt("i", Q("Fin", Id("d")), App(Id("n"), Id("i"))), Id("N"))), SubtypeOf("n", Arrow(Q("Fin", Id("d")), NatType), Equal(SumAt("i", Q("Fin", Id("d")), App(Id("n"), Id("i"))), Id("N"))), ComplexType)), Q("Matrix.diagonal", Lambda("i", Q("Fin", Id("d")), IfThenElse(Equal(Q("val", Id("i")), D(0)), Typed(D(1), ComplexType), D(0)))))))))),
                AssessedProvenance.FromLiterature(Note), Blocks(Paragraph(Text("The output reference projector is the input identity tensor the projector onto output level zero, Eq. (10), p. 2."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("occupationpartialtransposespectral-rg"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.RG"),
                H("RG"), StatementSource.FromAuthor(Disp(All("N", NatType, All("d", NatType, Equal(Q("RG", Id("N"), Id("d")), Q("Matrix.kronecker", Q("D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight", Mul(Q("RF", Id("N"), Id("d")), Q("outputReferenceProjector", Id("N"), Id("d")))), Typed(D(1), Q("Matrix", Q("Fin", Id("d")), Q("Fin", Id("d")), ComplexType)))))))),
                AssessedProvenance.FromLiterature(Note), Blocks(Paragraph(Text("RG is R_G of Eq. (10), p. 2: partial trace after multiplication by the reference projector, tensor the output identity."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("occupationpartialtransposespectral-a"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.A"),
                H("A"), StatementSource.FromAuthor(Disp(All("N", NatType, All("d", NatType, Equal(Q("A", Id("N"), Id("d")), Scale(Mul(Typed(Q("Nat.choose", Sub(Add(Id("N"), Id("d")), D(1)), Sub(Id("d"), D(1))), ComplexType), Typed(Add(Id("N"), Id("d")), ComplexType)), Q("RF", Id("N"), Id("d")))))))),
                AssessedProvenance.FromRepo(Note), Blocks(Paragraph(Text("The scaled A operator multiplies the corresponding fidelity operator by D(N,d)(N+d)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("occupationpartialtransposespectral-c"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.C"),
                H("C"), StatementSource.FromAuthor(Disp(All("N", NatType, All("d", NatType, Equal(Q("C", Id("N"), Id("d")), Scale(Mul(Typed(Q("Nat.choose", Sub(Add(Id("N"), Id("d")), D(1)), Sub(Id("d"), D(1))), ComplexType), Typed(Add(Id("N"), Id("d")), ComplexType)), Q("RG", Id("N"), Id("d")))))))),
                AssessedProvenance.FromRepo(Note), Blocks(Paragraph(Text("The scaled C operator multiplies the corresponding fidelity operator by D(N,d)(N+d)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("occupationpartialtransposespectral-blocks-blockindex"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.blockIndex"),
                H("Blocks.blockIndex"), StatementSource.FromAuthor(Disp(All("K", NatType, All("d", NatType, All("m", SubtypeOf("n", Arrow(Q("Fin", Id("d")), NatType), Equal(SumAt("i", Q("Fin", Id("d")), App(Id("n"), Id("i"))), Id("K"))), All("i", Q("Fin", Id("d")), Equal(Q("blockIndex", Id("m"), Id("i")), Pair(SubtypeValue(Q("Function.update", Q("val", Id("m")), Id("i"), Add(App(Q("val", Id("m")), Id("i")), D(1)))), Id("i"))))))))),
                AssessedProvenance.FromRepo(Note), Blocks(Paragraph(Text("A block index pairs the occupation m plus one particle at i with output level i; the subtype proof fixes total occupation K+1."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("occupationpartialtransposespectral-entryformula-dimension-pos"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.dimension_pos"),
                H("EntryFormula.dimension_pos"), StatementSource.FromAuthor(Disp(All("N", NatType, All("d", NatType, Implies(Leq(D(1), Id("d")), Less(D(0), Q("Nat.choose", Sub(Add(Id("N"), Id("d")), D(1)), Sub(Id("d"), D(1))))))))),
                AssessedProvenance.FromRepo(Note), Blocks(Paragraph(Text("The binomial dimension is positive for every nonempty alphabet."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("occupationpartialtransposespectral-scalar-blockmaximum"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.blockMaximum"),
                H("Scalar.blockMaximum"), StatementSource.FromAuthor(Disp(All("L", RealType, All("p", RealType, All("a", RealType, Equal(Q("blockMaximum", Id("L"), Id("p"), Id("a")), Add(Add(Id("p"), Mul(Sub(D(1), Id("p")), Id("a"))), Frac(Add(Add(Mul(Id("p"), Id("L")), Sub(D(1), Id("p"))), Q("Real.sqrt", Add(Square(Sub(Mul(Id("p"), Id("L")), Sub(D(1), Id("p")))), Mul(Mul(Mul(D(4), Id("p")), Sub(D(1), Id("p"))), Id("a"))))), D(2))))))))),
                AssessedProvenance.FromRepo(Note), Blocks(Paragraph(Text("The occupation block maximum consists of its scalar shift and the larger root of its rank-two part."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("occupationpartialtransposespectral-scalar-toproot"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.topRoot"),
                H("Scalar.topRoot"), StatementSource.FromAuthor(Disp(All("a", RealType, All("b", RealType, All("c", RealType, Equal(Q("topRoot", Id("a"), Id("b"), Id("c")), Frac(Add(Add(Id("a"), Id("c")), Q("Real.sqrt", Add(Square(Sub(Id("a"), Id("c"))), Mul(D(4), Square(Id("b")))))), D(2)))))))),
                AssessedProvenance.FromRepo(Note), Blocks(Paragraph(Text("The larger root of a real symmetric two by two matrix depends on its diagonal entries and off-diagonal coupling."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("occupationpartialtransposespectral-scalar-bottomroot"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.bottomRoot"),
                H("Scalar.bottomRoot"), StatementSource.FromAuthor(Disp(
                    All("d", RealType, All("s", RealType, All("t", RealType,
                        Equal(Q("bottomRoot", Id("d"), Id("s"), Id("t")),
                            Frac(Sub(Add(Id("d"), Id("t")),
                                Q("Real.sqrt", Add(Square(Sub(Id("d"), Id("t"))),
                                    Mul(D(4), Square(Id("s")))))), D(2)))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The smaller root of a real symmetric two by two matrix is the half-trace minus half the discriminant's square root."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("occupationpartialtransposespectral-scalar-toproot-sum"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.topRoot_sum"),
                H("Scalar.topRoot_sum"), StatementSource.FromAuthor(Disp(
                    All("d", RealType, All("s", RealType, All("t", RealType,
                        Equal(Add(Q("topRoot", Id("d"), Id("s"), Id("t")),
                                  Q("bottomRoot", Id("d"), Id("s"), Id("t"))),
                            Add(Id("d"), Id("t")))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The sum of the two roots equals the trace."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("occupationpartialtransposespectral-scalar-toproot-product"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.topRoot_product"),
                H("Scalar.topRoot_product"), StatementSource.FromAuthor(Disp(
                    All("d", RealType, All("s", RealType, All("t", RealType,
                        Equal(Mul(Q("topRoot", Id("d"), Id("s"), Id("t")),
                                  Q("bottomRoot", Id("d"), Id("s"), Id("t"))),
                            Sub(Mul(Id("d"), Id("t")), Square(Id("s"))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The product of the two roots equals the determinant."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("occupationpartialtransposespectral-scalar-toproot-bounds"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.topRoot_bounds"),
                H("Scalar.topRoot_bounds"), StatementSource.FromAuthor(Disp(All("d", RealType, All("s", RealType, All("t", RealType, And(Leq(Id("d"), Q("topRoot", Id("d"), Id("s"), Id("t"))), Leq(Id("t"), Q("topRoot", Id("d"), Id("s"), Id("t"))))))))),
                AssessedProvenance.FromRepo(Note), Blocks(Paragraph(Text("The larger root dominates both diagonal entries."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("occupationpartialtransposespectral-scalar-toproot-determinant"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.topRoot_determinant"),
                H("Scalar.topRoot_determinant"), StatementSource.FromAuthor(Disp(All("a", RealType, All("b", RealType, All("c", RealType, Equal(Mul(Sub(Q("topRoot", Id("a"), Id("b"), Id("c")), Id("a")), Sub(Q("topRoot", Id("a"), Id("b"), Id("c")), Id("c"))), Square(Id("b")))))))),
                AssessedProvenance.FromRepo(Note), Blocks(Paragraph(Text("The spectral gap product equals the square of the off-diagonal coupling."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("occupationpartialtransposespectral-scalar-toproot-quadratic-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.topRoot_quadratic_bound"),
                H("Scalar.topRoot_quadratic_bound"), StatementSource.FromAuthor(Disp(
                    All("a", RealType, All("b", RealType, All("c", RealType,
                    All("x", RealType, All("y", RealType,
                        Leq(Add(Add(Mul(Id("a"), Square(Id("x"))),
                                    Mul(Mul(Mul(D(2), Id("b")), Id("x")), Id("y"))),
                                Mul(Id("c"), Square(Id("y")))),
                            Mul(Q("topRoot", Id("a"), Id("b"), Id("c")),
                                Add(Square(Id("x")), Square(Id("y")))))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The quadratic form of a real symmetric two-by-two matrix is bounded above by its larger eigenvalue times the squared Euclidean length."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("occupationpartialtransposespectral-complex-distinguished-block-identity"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.distinguished_block_identity"),
                H("Complex.distinguished_block_identity"), StatementSource.FromAuthor(Disp(All("n", RealType, All("k", RealType, All("p", RealType, Implies(Leq(D(0), Mul(Id("n"), Id("k"))), Equal(Q("blockMaximum", Add(Id("n"), Id("k")), Id("p"), Id("n")), Q("topRoot", Add(Id("n"), D(1)), Mul(Id("p"), Q("Real.sqrt", Mul(Id("n"), Id("k")))), Add(Id("n"), Mul(Id("p"), Sub(Add(Id("k"), D(1)), Id("n")))))))))))),
                AssessedProvenance.FromRepo(Note), Blocks(Paragraph(Text("The block supported on the reference occupation has the stated two-dimensional root."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("occupationpartialtransposespectral-blockspectral-rankonequadratic"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.rankOneQuadratic"),
                H("BlockSpectral.rankOneQuadratic"), StatementSource.FromAuthor(Disp(
                    All("I", Id("Type"), Seq(OpenBracket, Q("Fintype", Id("I")), CloseBracket, Sp,
                        All("z", Arrow(Id("I"), ComplexType), All("psi", Arrow(Id("I"), ComplexType),
                            Equal(Q("dotProduct", Q("star", Id("z")),
                                Q("Matrix.mulVec", Q("Matrix.vecMulVec", Id("psi"), Q("star", Id("psi"))), Id("z"))),
                                Typed(Q("Complex.normSq", Q("dotProduct", Q("star", Id("z")), Id("psi"))), ComplexType)))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The quadratic form of a rank-one density matrix is the squared modulus of its overlap."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("occupationpartialtransposespectral-blockspectral-blockoperator"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.blockOperator"),
                H("BlockSpectral.blockOperator"), StatementSource.FromAuthor(Disp(All("I", Id("Type"), Seq(OpenBracket, Q("DecidableEq", Id("I")), CloseBracket, Sp, All("v", Arrow(Id("I"), RealType), All("i0", Id("I"), All("a", RealType, All("p", RealType, Equal(Q("blockOperator", Id("v"), Id("i0"), Id("a"), Id("p")), Add(Add(Scale(Typed(Add(Id("p"), Mul(Sub(D(1), Id("p")), Id("a"))), ComplexType), Typed(D(1), Q("Matrix", Id("I"), Id("I"), ComplexType))), Scale(Typed(Id("p"), ComplexType), Q("Matrix.vecMulVec", Lambda("i", Id("I"), Typed(App(Id("v"), Id("i")), ComplexType)), Lambda("i", Id("I"), Typed(App(Id("v"), Id("i")), ComplexType))))), Scale(Typed(Sub(D(1), Id("p")), ComplexType), Q("Matrix.diagonal", Lambda("i", Id("I"), IfThenElse(Equal(Id("i"), Id("i0")), D(1), D(0))))))))))))))),
                AssessedProvenance.FromRepo(Note), Blocks(Paragraph(Text("Each block is a scalar identity plus a real rank-one matrix and one coordinate projector."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("occupationpartialtransposespectral-blockspectral-blockoperator-quadratic"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.blockOperator_quadratic"),
                H("BlockSpectral.blockOperator_quadratic"), StatementSource.FromAuthor(Disp(All("I", Id("Type"), Instances(Id("I"), All("v", Arrow(Id("I"), RealType), All("i0", Id("I"), All("a", RealType, All("p", RealType, All("x", Arrow(Id("I"), ComplexType), Equal(Q("dotProduct", Q("star", Id("x")), Q("Matrix.mulVec", Q("blockOperator", Id("v"), Id("i0"), Id("a"), Id("p")), Id("x"))), Typed(Add(Add(Mul(Add(Id("p"), Mul(Sub(D(1), Id("p")), Id("a"))), SumAt("i", Id("I"), Q("Complex.normSq", App(Id("x"), Id("i"))))), Mul(Id("p"), Q("Complex.normSq", SumAt("i", Id("I"), Mul(Typed(App(Id("v"), Id("i")), ComplexType), App(Id("x"), Id("i"))))))), Mul(Sub(D(1), Id("p")), Q("Complex.normSq", App(Id("x"), Id("i0"))))), ComplexType))))))))))),
                AssessedProvenance.FromRepo(Note), Blocks(Paragraph(Text("The quadratic form is the sum of its norm, coherent rank-one score and reference-coordinate score."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("occupationpartialtransposespectral-blockmatrices-blockvector"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.blockVector"),
                H("BlockMatrices.blockVector"), StatementSource.FromAuthor(Disp(All("K", NatType, All("d", NatType, All("m", SubtypeOf("n", Arrow(Q("Fin", Id("d")), NatType), Equal(SumAt("i", Q("Fin", Id("d")), App(Id("n"), Id("i"))), Id("K"))), All("i", Q("Fin", Id("d")), Equal(Q("blockVector", Id("m"), Id("i")), Q("Real.sqrt", Add(Typed(App(Q("val", Id("m")), Id("i")), RealType), D(1)))))))))),
                AssessedProvenance.FromRepo(Note), Blocks(Paragraph(Text("The block vector has entries sqrt(m_i+1)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("occupationpartialtransposespectral-blockmatrices-weighted-block"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.weighted_block"),
                H("BlockMatrices.weighted_block"), StatementSource.FromAuthor(Disp(All("K", NatType, All("d", NatType, Implies(Leq(D(1), Id("d")), All("m", SubtypeOf("n", Arrow(Q("Fin", Id("d")), NatType), Equal(SumAt("i", Q("Fin", Id("d")), App(Id("n"), Id("i"))), Id("K"))), All("p", RealType, Equal(Q("Matrix.submatrix", Add(Scale(Typed(Id("p"), ComplexType), Q("A", Add(Id("K"), D(1)), Id("d"))), Scale(Typed(Sub(D(1), Id("p")), ComplexType), Q("C", Add(Id("K"), D(1)), Id("d")))), Q("blockIndex", Id("m")), Q("blockIndex", Id("m"))), Q("blockOperator", Q("blockVector", Id("m")), Typed(D(0), Q("Fin", Id("d"))), Add(Typed(App(Q("val", Id("m")), Typed(D(0), Q("Fin", Id("d")))), RealType), D(1)), Id("p")))))))))),
                AssessedProvenance.FromRepo(Note), Blocks(Paragraph(Text("Restricting the weighted fidelity operator to an occupation block gives its rank-one-plus-coordinate form."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("occupationpartialtransposespectral-globalbound-global-operator-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.global_operator_bound"),
                H("GlobalBound.global_operator_bound"), StatementSource.FromAuthor(Disp(All("K", NatType, All("k", NatType, Implies(Leq(D(1), Id("k")), All("p", RealType, Implies(Leq(D(0), Id("p")), Implies(Leq(Id("p"), D(1)), Q("Matrix.PosSemidef", Sub(Scale(Typed(Q("blockMaximum", Add(Add(Typed(Id("K"), RealType), Typed(Id("k"), RealType)), D(1)), Id("p"), Add(Typed(Id("K"), RealType), D(1))), ComplexType), Typed(D(1), Q("Matrix", Q("Prod", SubtypeOf("n", Arrow(Q("Fin", Add(Id("k"), D(1))), NatType), Equal(SumAt("i", Q("Fin", Add(Id("k"), D(1))), App(Id("n"), Id("i"))), Add(Id("K"), D(1)))), Q("Fin", Add(Id("k"), D(1)))), Q("Prod", SubtypeOf("n", Arrow(Q("Fin", Add(Id("k"), D(1))), NatType), Equal(SumAt("i", Q("Fin", Add(Id("k"), D(1))), App(Id("n"), Id("i"))), Add(Id("K"), D(1)))), Q("Fin", Add(Id("k"), D(1)))), ComplexType))), Q("AffineMap.lineMap", Q("C", Add(Id("K"), D(1)), Add(Id("k"), D(1))), Q("A", Add(Id("K"), D(1)), Add(Id("k"), D(1))), Typed(Id("p"), ComplexType)))))))))))),
                AssessedProvenance.FromRepo(Note), Blocks(Paragraph(Text("The exhaustive occupation partition and block Rayleigh bound show that the reference block dominates the complete operator, including isolated singletons."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => StrataLint.Scribe.FormulaDsl.Id(name);
    private static Formula NatType => Seq(Mathbb, Grp(Id("N")));
    private static Formula RealType => Seq(Mathbb, Grp(Id("R")));
    private static Formula ComplexType => Seq(Mathbb, Grp(Id("C")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Q(string name, params Formula[] args)
    {
        if (name == "Matrix.blockDiagonal'")
        {
            Formula symbol = Seq(Q("Matrix.blockDiagonal"), Apos);
            return args.Length == 0 ? symbol : new Formula.Apply(symbol, [.. args]);
        }
        Formula[] words = name.Split('.').Select(part => (Formula)Seq(Operatorname, Grp(Id(part)))).ToArray();
        Formula head = Seq(words.SelectMany((part, index) => index == 0 ? new[] {part} : new[] {Dot, part}).ToArray());
        return args.Length == 0 ? head : new Formula.Apply(head, [.. args]);
    }
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Field(Formula value, string field) => Seq(value, Dot, field == "1" ? D(1) : D(2));
    private static Formula Pair(Formula left, Formula right) => Parenthesized(Seq(left, Comma, Sp, right));
    private static Formula SubtypeValue(Formula value) => Seq(Langle, value, Rangle);
    private static Formula Scale(Formula scalar, Formula value) => Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(value));
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Frac(Formula left, Formula right) => new Formula.Fraction(left, right);
    private static Formula Square(Formula value) => new Formula.Power(value, D(2));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Leq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula All(string name, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Lambda(string name, Formula domain, Formula body) => Seq(Operatorname, Grp(Id("fun")), Sp, Typed(Id(name), domain), Sp, Mapsto, Sp, body);
    private static Formula SumAt(string name, Formula domain, Formula body) => Seq(new Formula.Subscript(Sum, Seq(Id(name), Colon, Sp, domain)), Parenthesized(body));
    private static Formula SubtypeOf(string name, Formula domain, Formula body) => Seq(OpenBrace, Id(name), Colon, Sp, domain, Sp, Slash, Slash, Sp, body, CloseBrace);
    private static Formula IfThenElse(Formula condition, Formula yes, Formula no) => Seq(Operatorname, Grp(Id("if")), Sp, Parenthesized(condition), Sp, Operatorname, Grp(Id("then")), Sp, yes, Sp, Operatorname, Grp(Id("else")), Sp, no);
    private static Formula Instances(Formula type, Formula body) => Seq(OpenBracket, Q("Fintype", type), CloseBracket, Sp, OpenBracket, Q("DecidableEq", type), CloseBracket, Sp, body);
}
