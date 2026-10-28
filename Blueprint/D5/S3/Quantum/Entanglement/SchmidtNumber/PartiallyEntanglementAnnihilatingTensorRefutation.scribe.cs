using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.SchmidtNumber;

internal sealed class PartiallyEntanglementAnnihilatingTensorRefutationDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Quantum/Entanglement/SchmidtNumber/PartiallyEntanglementAnnihilatingTensorRefutation";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/QuantumContext/mallickgangulymajumdar2026partialannihilating");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two non-local channels with Schmidt-number-two outputs can have an aligned tensor product with a Schmidt-rank-four output.",
        H("Partial entanglement annihilation fails under aligned tensor products"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nonlocal"),
                DeclarationHandle.Create(Module + ".NonLocal"),
                H("Excluding products of individual channels"),
                StatementSource.FromAuthor(Disp(NonLocalFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A linear map on the bipartite d by d system is non-local when it cannot "
                    + "be expressed as the tensor product of two completely positive, trace-preserving "
                    + "maps on the individual d-dimensional systems. This is the distinction in "
                    + "Section IV, main.tex line 630. The predicate only excludes such a factorization; "
                    + "complete positivity and trace preservation of the bipartite map are separate conditions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("is-pea"),
                DeclarationHandle.Create(Module + ".IsPEA"),
                H("Non-local partial entanglement annihilation"),
                StatementSource.FromAuthor(Disp(IsPEAFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A non-local r-partially entanglement annihilating channel is completely positive "
                    + "and trace preserving, is non-local, has r strictly below d, and sends every "
                    + "positive semidefinite trace-one input to an operator of Schmidt number at most r. "
                    + "This is Section IV, main.tex line 632. SchmidtNumberLE expresses the existence "
                    + "of a finite convex decomposition into normalized pure states whose coefficient "
                    + "matrices all have rank at most r, corresponding to the Schmidt-number definition "
                    + "in Section II, lines 261–265."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("aligned-tensor"),
                DeclarationHandle.Create(Module + ".alignedTensor"),
                H("The tensor product across the aligned split"),
                StatementSource.FromAuthor(Disp(AlignedTensorFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The equivalence a first exchanges the middle two factors of the fourfold "
                    + "product and then identifies each pair of Fin d indices with Fin (d * d). "
                    + "The linear equivalence t reindexes both matrix indices by a. Conjugating "
                    + "the tensor product of e and f by t makes the two first subsystems one party "
                    + "and the two second subsystems the other party. Thus both parties have "
                    + "dimension d * d."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("Closure at the same Schmidt-number threshold"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For all natural dimensions d and thresholds r, the assertion says that any "
                    + "two non-local r-partially entanglement annihilating channels remain in that "
                    + "class after taking their aligned tensor product. The threshold stays r "
                    + "while the local dimension becomes d * d. This is a precise closure assertion "
                    + "for the tensor-product question in the Conclusion, main.tex line 1167; "
                    + "the source asks the question without asserting this closure."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Two qutrit channels disprove closure"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take d = 3 and r = 2. Let φ be the normalized vector "
                        + "(|00⟩ + |11⟩)/√2 and let R send X to Tr(X)|φ⟩⟨φ|. "
                        + "The coefficient matrix of φ is diagonal with entries 1/√2, 1/√2 and 0. "
                        + "Its two nonzero diagonal entries give rank two.")),
                    Paragraph(Text(
                        "For each coordinate vector |j⟩ of the nine-dimensional input, use the "
                        + "Kraus operator |φ⟩⟨j|. Summing their actions gives exactly R, so R is "
                        + "completely positive. Its output trace equals the input trace because "
                        + "|φ⟩⟨φ| has trace one; hence R is trace preserving.")),
                    Paragraph(Text(
                        "Suppose R were a tensor product of two individual channels. Evaluating "
                        + "it on |00⟩⟨00| would express |φ⟩⟨φ| as A ⊗ B, where A and B are "
                        + "the individual outputs on |0⟩⟨0|. The diagonal entries at (0,0) and "
                        + "(1,1) are both (1/√2)², which is nonzero, whereas the entry at (0,1) "
                        + "is zero. Thus A₀₀B₁₁ = 0. If A₀₀ = 0 then A₀₀B₀₀ is zero, "
                        + "and if B₁₁ = 0 then A₁₁B₁₁ is zero. Either case contradicts one "
                        + "of the two nonzero diagonal entries, so R is non-local.")),
                    Paragraph(Text(
                        "On every trace-one input, R outputs |φ⟩⟨φ|. The one-term convex "
                        + "decomposition with weight one therefore gives Schmidt number at most "
                        + "two. Together with complete positivity, trace preservation, non-locality "
                        + "and 2 < 3, this makes R a non-local 2-partially entanglement annihilating channel.")),
                    Paragraph(Text(
                        "Let ψ be φ ⊗ φ regrouped across the aligned split. In the Fin 9 "
                        + "coordinates its coefficient matrix is diagonal, with entry 1/2 at "
                        + "indices 0, 1, 3 and 4 and zero elsewhere. Its rank is therefore four.")),
                    Paragraph(Text(
                        "For any normalized bipartite vector u, a convex decomposition of "
                        + "|u⟩⟨u| with coefficient ranks at most r forces the coefficient rank "
                        + "of u to be at most r. Indeed, nonnegative weights summing to one "
                        + "are individually at most one and include a positive weight. The "
                        + "pure-state decomposition property then identifies that component "
                        + "with z times u for a complex scalar z of norm one. Its coefficient "
                        + "matrix is z times the coefficient matrix of u; since z is nonzero, "
                        + "the ranks agree, giving the required rank bound.")),
                    Paragraph(Text(
                        "Expanding the tensor product of the two trace-and-prepare maps on "
                        + "matrix units shows that it sends X to Tr(X) times "
                        + "(|φ⟩⟨φ| ⊗ |φ⟩⟨φ|). Reindexing preserves trace. On the aligned "
                        + "input |ψ⟩⟨ψ| this trace is one, and the reindexed output is "
                        + "|ψ⟩⟨ψ| itself, as follows by multiplying the vector coordinates.")),
                    Paragraph(Text(
                        "If the aligned tensor product were non-local 2-partially entanglement "
                        + "annihilating, its Schmidt-number bound on the positive semidefinite "
                        + "trace-one input |ψ⟩⟨ψ| would give Schmidt number at most two for "
                        + "that same pure output. The pure-state rank bound would then imply "
                        + "4 ≤ 2, a contradiction. Applying the closure assertion to d = 3, "
                        + "r = 2 and e = f = R would give precisely this impossible conclusion."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mallick-ganguly-majumdar-2026-pea-tensor-nonclosure"),
                    ResolutionKind.Refuted)))));

    private static Formula NonLocalFormula() => All("d", Naturals(), All("e", BipartiteMaps(),
        IffOf(LocalCall("NonLocal", X("e")), new Formula.Not(Parenthesized(
            Some("e₁", IndividualMaps(), Some("e₂", IndividualMaps(),
                And(CPTP(X("e₁")), And(CPTP(X("e₂")),
                    Equal(X("e"), At(Qualified("MatrixMap", "kron"), X("e₁"), X("e₂"))))))))))));

    private static Formula IsPEAFormula() => All("d", Naturals(), All("r", Naturals(),
        All("e", BipartiteMaps(), IffOf(LocalCall("IsPEA", X("d"), X("r"), X("e")),
            And(CPTP(X("e")), And(LocalCall("NonLocal", X("e")), And(
                new Formula.Relation(X("r"), FormulaRelationOperator.LessThan, X("d")),
                All("ρ", At(Schmidt("BipartiteOp"), X("d")),
                    Arrow(At(Qualified("Matrix", "PosSemidef"), Rho),
                        Arrow(Equal(At(Qualified("Matrix", "trace"), Rho), Typed(D(1), Complexes())),
                            At(Schmidt("SchmidtNumberLE"), At(Qualified("DFunLike", "coe"), X("e"), Rho),
                                X("r"))))))))))));

    private static Formula AlignedTensorFormula()
    {
        Formula a = At(Qualified("Equiv", "trans"),
            At(Qualified("Equiv", "prodProdProdComm"), FinOf(X("d")), FinOf(X("d")),
                FinOf(X("d")), FinOf(X("d"))),
            At(Qualified("Equiv", "prodCongr"), Qualified("finProdFinEquiv"), Qualified("finProdFinEquiv")));
        Formula t = At(Qualified("Matrix", "reindexLinearEquiv"), Complexes(), Complexes(), X("a"), X("a"));
        Formula composition = At(Qualified("LinearMap", "comp"),
            At(Qualified("LinearEquiv", "toLinearMap"), X("t")),
            At(Qualified("LinearMap", "comp"), At(Qualified("MatrixMap", "kron"), X("e"), X("f")),
                At(Qualified("LinearEquiv", "toLinearMap"), At(Qualified("LinearEquiv", "symm"), X("t")))));
        return All("d", Naturals(), All("e", BipartiteMaps(), All("f", BipartiteMaps(),
            Equal(LocalCall("alignedTensor", X("e"), X("f")),
                Let("a", a, Let("t", t, composition))))));
    }

    private static Formula ClaimFormula() => IffOf(Local("claim"),
        All("d", Naturals(), All("r", Naturals(), All("e", BipartiteMaps(), All("f", BipartiteMaps(),
            Arrow(LocalCall("IsPEA", X("d"), X("r"), X("e")),
                Arrow(LocalCall("IsPEA", X("d"), X("r"), X("f")),
                    LocalCall("IsPEA", Multiply(X("d"), X("d")), X("r"),
                        LocalCall("alignedTensor", X("e"), X("f"))))))))));

    private static Formula X(string name) => name switch
    {
        "e₁" => new Formula.Subscript(F.Id("e"), D(1)),
        "e₂" => new Formula.Subscript(F.Id("e"), D(2)),
        "ρ" => Rho,
        _ => F.Id(name),
    };
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) => Qualified(
        "D5", "S3", "Quantum", "Entanglement", "SchmidtNumber",
        "PartiallyEntanglementAnnihilatingTensorRefutation", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula Schmidt(string name) => Qualified(
        "D5", "S3", "Quantum", "Entanglement", "TavakoliMorelliIncompleteEAM", name);
    private static Formula CPTP(Formula e) => At(Qualified(
        "D5", "S3", "Quantum", "QuantumChannels", "ChannelAssemblageLOSRRefutation", "IsCPTP"), e);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula Pairs() => Parenthesized(Seq(FinOf(X("d")), Sp, Times, Sp, FinOf(X("d"))));
    private static Formula IndividualMaps() => At(Qualified("MatrixMap"), FinOf(X("d")), FinOf(X("d")), Complexes());
    private static Formula BipartiteMaps() => At(Qualified("MatrixMap"), Pairs(), Pairs(), Complexes());
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Let(string name, Formula value, Formula body) => Parenthesized(Seq(
        Qualified("let"), Sp, X(name), Sp, Colon, Eq, Sp, value, Semi, Sp, body));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(Parenthesized(a), Parenthesized(b));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula IffOf(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Multiply(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
}
