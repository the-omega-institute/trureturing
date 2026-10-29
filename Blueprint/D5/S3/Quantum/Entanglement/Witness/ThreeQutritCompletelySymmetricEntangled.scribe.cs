using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Witness;

internal sealed class ThreeQutritCompletelySymmetricEntangledDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Entanglement/Witness/ThreeQutritCompletelySymmetricEntangled";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Entropy/chenchuqianshen2019cs");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A completely symmetric density matrix on three qutrits has no fully separable decomposition.",
        H("An entangled completely symmetric three-qutrit density matrix"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("completely-symmetric"),
                DeclarationHandle.Create(Module + ".IsCompletelySymmetric"),
                H("Complete symmetry of all index positions"),
                StatementSource.FromAuthor(Disp(CompletelySymmetricFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A word is a function from Fin d to Fin 3. The two copies of Fin d label the ket and bra positions. "
                    + "Every permutation of their disjoint union rearranges all twice d positions, including permutations that mix the ket and bra. "
                    + "The matrix entry must remain unchanged. This is Definition 1 of the source, arXiv:1812.04182v4, CSv2.tex lines 360–391, with local dimension three. "
                    + "The predicate is defined for every complex matrix and every natural d; positivity and trace one are separate conditions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fully-separable"),
                DeclarationHandle.Create(Module + ".IsFullySeparable"),
                H("Finite mixtures of unit product projectors"),
                StatementSource.FromAuthor(Disp(FullySeparableFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Choose a finite number n of summands, strictly positive real weights wt summing to one, and a unit complex vector v i k for each summand i and subsystem k. "
                    + "The sum of squared complex norms of each local vector is one. The multilinear product map forms the product vector, and its outer product with its pointwise conjugate forms its rank-one projector. "
                    + "The real weight is included in the complex scalars before scalar multiplication of that projector. "
                    + "The constant family of multiplication maps is indexed by the word type. "
                    + "This specializes the source's convex-mixture definition at CSv2.tex lines 244–252 and its multipartite definition of full separability at lines 444–452."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The universal multi-qutrit separability assertion"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural d at least three, every positive semidefinite complex matrix of trace one on d qutrits is fully separable whenever it is completely symmetric. "
                    + "This is the universal assertion associated with the source's question, ‘Are multi-qutrit CS states separable?’, at CSv2.tex line 1857. "
                    + "The quantifier starts at three subsystems; it makes no assertion about two qutrits."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("A three-qutrit counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For a three-letter word, its occupation tuple records the numbers of zeros, ones and twos. "
                        + "Each coordinate is the sum of its three equality indicators, and summing over words is summing independently over their three letters. "
                        + "The ten possible occupation tuples are (3,0,0), (1,2,0), (1,0,2), (0,3,0), (2,1,0), (0,1,2), (0,0,3), (2,0,1), (0,2,1) and (1,1,1). "
                        + "Define a real function y of the combined occupation tuple by the nonzero values "
                        + "y(6,0,0) = y(0,6,0) = 132; y(0,0,6) = 3; "
                        + "y(4,2,0) = y(2,4,0) = y(2,2,2) = 4; "
                        + "y(4,0,2) = y(0,4,2) = 20; and y(2,0,4) = y(0,2,4) = 6, with zero elsewhere. "
                        + "Let ρ have entry y(q)/471, included from the reals into the complex numbers, when q is the sum of the two word occupation tuples. "
                        + "A permutation of the six positions preserves each combined letter count: the two indicator sums are one sum over the disjoint union, invariant under reindexing by the permutation. "
                        + "Thus ρ is completely symmetric.")),
                    Paragraph(Text(
                        "For each occupation tuple q, let e_q be the complex-valued indicator of its word class. "
                        + "Use the seven vectors e_(3,0,0) + e_(1,2,0) + e_(1,0,2), 8e_(3,0,0) + e_(1,0,2), "
                        + "e_(0,3,0) + e_(2,1,0) + e_(0,1,2), 8e_(0,3,0) + e_(0,1,2), "
                        + "e_(0,0,3) + 2e_(2,0,1) + 2e_(0,2,1), e_(2,0,1) − e_(0,2,1), and e_(1,1,1). "
                        + "The matrix ρ is the sum of their rank-one projectors with respective weights 4, 2, 4, 2, 3, 8 and 4, all divided by 471. "
                        + "This identity follows by evaluating the hundred pairs of occupation classes. Each projector and each weighted term is positive semidefinite, hence so is their sum. "
                        + "The real trace numerator is 2·132 + 3 + 6·4 + 6·20 + 6·6 + 6·4 = 471; every diagonal entry has zero imaginary part. "
                        + "Therefore ρ has trace one.")),
                    Paragraph(Text(
                        "Consider any decomposition of ρ into rank-one projectors with strictly positive real weights wt j and vectors ψ j. "
                        + "If words a and b have the same occupation tuple, the four entries give "
                        + "ρ(a,a) + ρ(b,b) − ρ(a,b) − ρ(b,a) = 0. "
                        + "Expanding those entries and taking real parts gives the sum of wt j times the squared norm of ψ j a − ψ j b equal to zero. "
                        + "Every summand is nonnegative, and every weight is strictly positive, so each difference vanishes. "
                        + "Thus every vector in such a decomposition is constant on each occupation class.")),
                    Paragraph(Text(
                        "A product vector with this constancy is a scalar multiple of a third tensor power. "
                        + "For the zero vector choose scalar zero and the zero local vector. Otherwise choose a word w where its product amplitude is nonzero, so all three local factors there are nonzero. "
                        + "Swapping the first two letters and then the first and third letters preserves occupation tuples. "
                        + "Canceling the corresponding nonzero factors in these two identities shows that the second local vector is the first multiplied by v 1 (w 0) / v 0 (w 0), "
                        + "and the third is the first multiplied by v 2 (w 0) / v 0 (w 0). "
                        + "Consequently the product amplitude at any word is c times the product of the coordinates of x, "
                        + "where x is v 0 and c is the product of those two ratios.")),
                    Paragraph(Text(
                        "For nonnegative real a, b and c, the three-term arithmetic–geometric mean inequality with equal weights one third, applied to a²b, ab² and c³, gives "
                        + "a²b + ab² + c³ − 3abc ≥ 0, since their product is (abc)³. "
                        + "Define a diagonal real functional W on words by assigning one third to occupation tuples (2,1,0) and (1,2,0), one to (0,0,3), minus one half to (1,1,1), and zero elsewhere. "
                        + "For a scalar multiple of a third tensor power its value is the squared norm of the scalar times "
                        + "a²b + ab² + c³ − 3abc, where a, b and c are the squared norms of the three coordinates of the local vector. "
                        + "Expanding over the 27 words proves this identity. The preceding inequality makes the value nonnegative, "
                        + "so it is nonnegative for every product vector constant on occupation classes.")),
                    Paragraph(Text(
                        "Direct evaluation on ρ gives the W-weighted diagonal sum (4 + 4 + 3 − 12)/471 = −1/471. "
                        + "If ρ were fully separable, its product vectors would be constant on occupation classes by the positive-weight argument. "
                        + "Its real diagonal entries would be sums of the positive weights times the squared norms of those product amplitudes. "
                        + "Interchanging the two finite sums would express the W-weighted diagonal sum as a sum of nonnegative terms. "
                        + "This contradicts its strictly negative value, proving that ρ is entangled. "
                        + "Finally, applying the universal assertion at d = 3 to the positive semidefinite, trace-one, completely symmetric matrix ρ would make it fully separable, yielding the contradiction."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("chen-chu-qian-shen-2019-multi-qutrit-completely-symmetric-separability"),
                    ResolutionKind.Refuted)))));

    private static Formula CompletelySymmetricFormula()
    {
        Formula positions = At(Qualified("Sum"), FinOf(X("d")), FinOf(X("d")));
        Formula Permuted(string injection) => LambdaOf("k", FinOf(X("d")),
            At(Qualified("Sum", "elim"), X("i"), X("j"),
                At(Qualified("Equiv", "toFun"), X("π"), At(Qualified("Sum", injection), X("k")))));
        Formula body = All("π", At(Qualified("Equiv", "Perm"), positions),
            All("i", WordType(), All("j", WordType(),
                Equal(At(X("ρ"), Permuted("inl"), Permuted("inr")), At(X("ρ"), X("i"), X("j"))))));
        return MatrixBinders(Equivalence(LocalCall("IsCompletelySymmetric", X("ρ")), body));
    }

    private static Formula FullySeparableFormula()
    {
        Formula productMap = At(Qualified("MultilinearMap", "piFamily"),
            At(Qualified("Function", "const"), WordType(),
                At(Qualified("MultilinearMap", "mkPiAlgebra"), Complexes(), FinOf(X("d")), Complexes())));
        Formula product = At(Qualified("DFunLike", "coe"), productMap, At(X("v"), X("i")));
        Formula projector = At(Qualified("Matrix", "vecMulVec"), product, At(Qualified("Star", "star"), product));
        Formula weighted = At(Qualified("HSMul", "hSMul"),
            At(Qualified("Complex", "ofReal"), At(X("wt"), X("i"))), projector);
        Formula body = Some("n", Naturals(), Some("wt", Arrow(FinOf(X("n")), Reals()),
            Some("v", Arrow(FinOf(X("n")), Arrow(FinOf(X("d")), Arrow(FinOf(D(3)), Complexes()))),
                Conjunction(All("i", FinOf(X("n")), Less(D(0), At(X("wt"), X("i")))),
                    Conjunction(Equal(SumOver("i", FinOf(X("n")), At(X("wt"), X("i"))), D(1)),
                        Conjunction(All("i", FinOf(X("n")), All("k", FinOf(X("d")),
                                Equal(SumOver("j", FinOf(D(3)), At(Qualified("Complex", "normSq"),
                                    At(X("v"), X("i"), X("k"), X("j")))), D(1)))),
                            Equal(X("ρ"), SumOver("i", FinOf(X("n")), weighted))))))));
        return MatrixBinders(Equivalence(LocalCall("IsFullySeparable", X("ρ")), body));
    }

    private static Formula ClaimFormula() => Equivalence(Local("claim"),
        All("d", Naturals(), Arrow(LE(D(3), X("d")), All("ρ", MatrixType(),
            Arrow(At(Qualified("D5", "S3", "Quantum", "Information", "SLDSpectralEnergy", "IsDensity"), X("ρ")),
                Arrow(LocalCall("IsCompletelySymmetric", X("ρ")), LocalCall("IsFullySeparable", X("ρ"))))))));

    private static Formula MatrixBinders(Formula body) => All("d", Naturals(), All("ρ", MatrixType(), body));
    private static Formula MatrixType() => At(Qualified("Matrix"), WordType(), WordType(), Complexes());
    private static Formula WordType() => At(Qualified("D5", "S3", "Quantum", "Entanglement", "OccupancyWordSectors", "Word"), FinOf(D(3)), X("d"));
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Entanglement", "Witness", "ThreeQutritCompletelySymmetricEntangled", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula X(string name) => name switch { "ρ" => Rho, "π" => Pi, _ => F.Id(name) };
    private static Formula Qualified(params string[] parts) => Seq(Operatorname,
        Grp(Seq(parts.SelectMany((part, index) => index == 0 ? new[] { F.Id(part) } : new[] { Dot, F.Id(part) }).ToArray())));
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula body) => Seq(Left, Open, body, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) => Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) => Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) => At(Qualified("Finset", "sum"),
        Typed(Qualified("Finset", "univ"), At(Qualified("Finset"), type)), LambdaOf(name, type, body));
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Conjunction(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
}
