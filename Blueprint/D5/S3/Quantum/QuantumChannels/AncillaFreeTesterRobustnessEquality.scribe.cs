using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class AncillaFreeTesterRobustnessEqualityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/QuantumChannels/AncillaFreeTesterRobustnessEquality";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/Observer/sedlakreitznerchiribellaziman2016testers");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ancilla-free testers with a common normalization state have the robustness of their canonical POVMs.",
        H("Robustness of ancilla-free testers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("is-tester"), DeclarationHandle.Create(Module + ".IsTester"),
                H("Quantum testers"), StatementSource.FromAuthor(Disp(IsTesterFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A tester is a finite family t of positive semidefinite effects on the output-input tensor product. "
                    + "Its sum is the output identity tensored with a density matrix σ on the input. "
                    + "Here IsDensity means positive semidefinite with complex trace equal to one. "
                    + "This is the tester definition in ti_pra_07.tex, lines 247–259."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tester-compatible-at"), DeclarationHandle.Create(Module + ".TesterCompatibleAt"),
                H("Compatibility after adding tester noise"),
                StatementSource.FromAuthor(Disp(TesterCompatibleFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The noise testers e and f have the outcome types of a and b. A joint tester c has outcomes j × k, "
                    + "and its marginals are the two mixtures at the same real weight lam. "
                    + "The three testers may have different normalization states, and the noise need not be ancilla-free. "
                    + "The predicate itself allows every real lam; robustness restricts lam to the unit interval. "
                    + "These are the marginal and noise conditions in ti_pra_07.tex, lines 451–459 and 567–570."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tester-robustness"), DeclarationHandle.Create(Module + ".testerRobustness"),
                H("Tester robustness"), StatementSource.FromAuthor(Disp(TesterRobustnessFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Tester robustness is the infimum of the real weights in the closed unit interval for which "
                    + "separate tester noises give compatible mixtures. The source uses a minimum "
                    + "in ti_pra_07.tex, lines 574–577; this infimum formulation makes no assertion of attainment."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("povm-compatible-at"), DeclarationHandle.Create(Module + ".POVMCompatibleAt"),
                H("Compatibility after adding measurement noise"),
                StatementSource.FromAuthor(Disp(POVMCompatibleFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The families u, v and g are POVMs: every effect is positive semidefinite and each whole family sums "
                    + "to the identity. The two marginals of g are the mixtures of p and q with the separate noises u and v. "
                    + "All scalar actions in these formulas use real scalars on complex matrices. "
                    + "The measurement noise condition is stated in ti_pra_07.tex, lines 761–765."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("povm-robustness"), DeclarationHandle.Create(Module + ".povmRobustness"),
                H("Measurement robustness"), StatementSource.FromAuthor(Disp(POVMRobustnessFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Measurement robustness is the infimum of the weights in the closed unit interval that permit "
                    + "a joint POVM after adding separate noise POVMs. It expresses the robustness of "
                    + "ti_pra_07.tex, lines 767–770, using an infimum without asserting attainment."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"), DeclarationHandle.Create(Module + ".claim"),
                H("Equality for a common ancilla-free state"),
                StatementSource.FromAuthor(Disp(Equivalence(Local("claim"), ClaimBody()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For arbitrary finite output and input types y and x and outcome types j and k, take a common density "
                    + "matrix ρ and output POVMs m and n. Their ancilla-free testers have effects m(a) ⊗ ρ and n(b) ⊗ ρ. "
                    + "The associated canonical POVMs have effects m(a) ⊗ I and n(b) ⊗ I on y × Fin(rank ρ), "
                    + "using coordinates on the support of ρ. The equality concerns precisely these two robustness values. "
                    + "The product characterization is Proposition 3, ti_pra_07.tex, lines 333–338; "
                    + "the canonical POVM is defined at lines 281–303. The common-state setting appears at line 772 "
                    + "and the ancilla-free question at line 807."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"), DeclarationHandle.Create(Module + ".result"),
                H("Equality of tester and canonical measurement robustness"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "First, tensoring each effect of a POVM with ρ gives a tester: Kronecker products preserve "
                        + "positive semidefiniteness, and the effects sum to I ⊗ ρ. Conversely, take the partial trace "
                        + "over x of each tester effect. This preserves positive semidefiniteness and finite sums. "
                        + "A tester normalized by any density matrix σ is sent to a POVM because "
                        + "the partial trace of I ⊗ σ is (tr σ)I = I.")),
                    Paragraph(Text(
                        "For a fixed lam, suppose u, v and g are noise and joint POVMs for m and n. "
                        + "Tensor all three families with ρ. Distributing the Kronecker product over the marginal sums, "
                        + "addition and real scalar multiplication gives noise and joint testers for m ⊗ ρ and n ⊗ ρ. "
                        + "In the reverse direction, start with arbitrary noise testers e and f and a joint tester c. "
                        + "Apply the partial trace over x to all three families and their marginal equations. "
                        + "They become POVMs, and tr ρ = 1 sends m(a) ⊗ ρ to m(a) and n(b) ⊗ ρ to n(b). "
                        + "Thus compatibility at lam is equivalent for the product testers and the output POVMs, "
                        + "even when e, f and c have different normalization states.")),
                    Paragraph(Text(
                        "Next tensor noise and joint POVMs with the identity on Fin r. Positivity, unit normalization "
                        + "and the marginal equations are preserved. For the reverse direction assume 0 < r and "
                        + "compress every effect to the principal submatrix indexed by pairs (b,0). "
                        + "Principal submatrices preserve positivity. The inclusion b ↦ (b,0) is injective, "
                        + "so compression preserves the identity, and it commutes with finite sums, addition and "
                        + "real scalar multiplication. The compressed entries of t ⊗ I are exactly the entries of t. "
                        + "Consequently compression turns noise and joint POVMs on y × Fin r into noise and joint "
                        + "POVMs on y with the required marginals.")),
                    Paragraph(Text(
                        "The trace equation tr ρ = 1 implies ρ ≠ 0, hence some column has a nonzero entry. "
                        + "The span of the columns therefore has positive dimension, giving 0 < rank ρ. "
                        + "The first pair of implications identifies the feasible weights in [0,1] for the product testers "
                        + "with those for m and n. The tensor and compression implications identify the latter set "
                        + "with the feasible weights for the canonical POVMs when r = rank ρ. "
                        + "Composing these set equalities and taking infima proves the displayed equality. "
                        + "No minimizer or numerical robustness value is needed."))),
                DescribeRole.Theorem))));

    private static Formula IsTesterFormula()
    {
        Formula space = TensorSpace("y", "x");
        Formula body = Conjunction(All("a", X("j"), Positive(At(X("t"), X("a")))),
            Some("σ", MatrixOf(X("x")), Conjunction(Density(X("σ")),
                Equal(SumOver("a", X("j"), At(X("t"), X("a"))),
                    Tensor(Identity(X("y")), X("σ"))))));
        return TesterTypes(false, All("t", Family("j", space),
            Equivalence(LocalCall("IsTester", X("t")), body)));
    }

    private static Formula TesterCompatibleFormula()
    {
        Formula space = TensorSpace("y", "x");
        Formula body = Some("e", Family("j", space), Some("f", Family("k", space),
            Some("c", Arrow(Product(X("j"), X("k")), MatrixOf(space)),
                Conjunction(LocalCall("IsTester", X("e")),
                    Conjunction(LocalCall("IsTester", X("f")),
                        Conjunction(LocalCall("IsTester", X("c")),
                            Conjunction(
                                All("u", X("j"), Equal(SumOver("v", X("k"),
                                    At(X("c"), Pair(X("u"), X("v")))),
                                    Mixture(X("a"), X("e"), X("u")))),
                                All("v", X("k"), Equal(SumOver("u", X("j"),
                                    At(X("c"), Pair(X("u"), X("v")))),
                                    Mixture(X("b"), X("f"), X("v")))))))))));
        return TesterTypes(true, All("lam", Reals(), All("a", Family("j", space),
            All("b", Family("k", space), Equivalence(
                LocalCall("TesterCompatibleAt", X("lam"), X("a"), X("b")), body)))));
    }

    private static Formula TesterRobustnessFormula()
    {
        Formula space = TensorSpace("y", "x");
        return TesterTypes(true, All("a", Family("j", space), All("b", Family("k", space),
            Equal(Typed(LocalCall("testerRobustness", X("a"), X("b")), Reals()),
                Infimum(LocalCall("TesterCompatibleAt", X("lam"), X("a"), X("b")))))));
    }

    private static Formula POVMCompatibleFormula()
    {
        Formula space = X("z");
        Formula body = Some("u", Family("j", space), Some("v", Family("k", space),
            Some("g", Arrow(Product(X("j"), X("k")), MatrixOf(space)),
                Conjunction(POVM("u", "a", X("j"), space),
                    Conjunction(POVM("v", "b", X("k"), space),
                        Conjunction(POVM("g", "ab", Product(X("j"), X("k")), space),
                            Conjunction(
                                All("a", X("j"), Equal(SumOver("b", X("k"),
                                    At(X("g"), Pair(X("a"), X("b")))),
                                    Mixture(X("p"), X("u"), X("a")))),
                                All("b", X("k"), Equal(SumOver("a", X("j"),
                                    At(X("g"), Pair(X("a"), X("b")))),
                                    Mixture(X("q"), X("v"), X("b")))))))))));
        return POVMTypes(All("lam", Reals(), All("p", Family("j", space),
            All("q", Family("k", space), Equivalence(
                LocalCall("POVMCompatibleAt", X("lam"), X("p"), X("q")), body)))));
    }

    private static Formula POVMRobustnessFormula() => POVMTypes(
        All("p", Family("j", X("z")), All("q", Family("k", X("z")),
            Equal(Typed(LocalCall("povmRobustness", X("p"), X("q")), Reals()),
                Infimum(LocalCall("POVMCompatibleAt", X("lam"), X("p"), X("q")))))));

    private static Formula ClaimBody()
    {
        Formula rankSpace = At(Qualified("Fin"), At(Qualified("Matrix", "rank"), X("ρ")));
        Formula equality = Equal(
            LocalCall("testerRobustness",
                LambdaOf("a", X("j"), Tensor(At(X("m"), X("a")), X("ρ"))),
                LambdaOf("b", X("k"), Tensor(At(X("n"), X("b")), X("ρ")))),
            LocalCall("povmRobustness",
                LambdaOf("a", X("j"), Tensor(At(X("m"), X("a")), Identity(rankSpace))),
                LambdaOf("b", X("k"), Tensor(At(X("n"), X("b")), Identity(rankSpace)))));
        Formula body = All("ρ", MatrixOf(X("x")), All("m", Family("j", X("y")),
            All("n", Family("k", X("y")), Arrow(Density(X("ρ")),
                Arrow(POVM("m", "a", X("j"), X("y")),
                    Arrow(POVM("n", "b", X("k"), X("y")), equality))))));
        body = Instances(body,
            At(Qualified("Fintype"), X("y")), At(Qualified("DecidableEq"), X("y")),
            At(Qualified("Fintype"), X("x")), At(Qualified("DecidableEq"), X("x")),
            At(Qualified("Fintype"), X("j")), At(Qualified("DecidableEq"), X("j")),
            At(Qualified("Fintype"), X("k")), At(Qualified("DecidableEq"), X("k")));
        return All("y", Qualified("Type"), All("x", Qualified("Type"),
            All("j", Qualified("Type"), All("k", Qualified("Type"), body))));
    }

    private static Formula TesterTypes(bool withK, Formula body)
    {
        Formula[] instances = withK
            ? [At(Qualified("Fintype"), X("y")), At(Qualified("DecidableEq"), X("y")),
                At(Qualified("Fintype"), X("x")), At(Qualified("Fintype"), X("j")),
                At(Qualified("Fintype"), X("k"))]
            : [At(Qualified("Fintype"), X("y")), At(Qualified("DecidableEq"), X("y")),
                At(Qualified("Fintype"), X("x")), At(Qualified("Fintype"), X("j"))];
        body = Instances(body, instances);
        if (withK) body = All("k", Qualified("Type"), body);
        return All("y", Qualified("Type"), All("x", Qualified("Type"),
            All("j", Qualified("Type"), body)));
    }

    private static Formula POVMTypes(Formula body) => All("z", Qualified("Type"),
        All("j", Qualified("Type"), All("k", Qualified("Type"), Instances(body,
            At(Qualified("Fintype"), X("z")), At(Qualified("DecidableEq"), X("z")),
            At(Qualified("Fintype"), X("j")), At(Qualified("Fintype"), X("k"))))));

    private static Formula Instances(Formula body, params Formula[] instances)
    {
        for (var i = instances.Length - 1; i >= 0; i--)
            body = Seq(OpenBracket, instances[i], CloseBracket, Comma, Sp, Parenthesized(body));
        return body;
    }

    private static Formula POVM(string family, string index, Formula outcomes, Formula space) =>
        Conjunction(All(index, outcomes, Positive(At(X(family), X(index)))),
            Equal(SumOver(index, outcomes, At(X(family), X(index))), Identity(space)));
    private static Formula Infimum(Formula predicate) => At(Qualified("sInf"),
        Seq(OpenBrace, Typed(X("lam"), Reals()), Sp, Mid, Sp,
            Conjunction(LE(Typed(D(0), Reals()), X("lam")),
                Conjunction(LE(X("lam"), Typed(D(1), Reals())), predicate)), CloseBrace));
    private static Formula Mixture(Formula original, Formula noise, Formula index) =>
        new Formula.Binary(
            Smul(new Formula.Binary(Typed(D(1), Reals()), FormulaBinaryOperator.Subtract, X("lam")),
                At(original, index)), FormulaBinaryOperator.Add, Smul(X("lam"), At(noise, index)));
    private static Formula Smul(Formula scalar, Formula matrix) =>
        At(Qualified("HSMul", "hSMul"), scalar, matrix);
    private static Formula Positive(Formula matrix) => At(Qualified("Matrix", "PosSemidef"), matrix);
    private static Formula Density(Formula matrix) =>
        At(Qualified("D5", "S3", "Quantum", "Information", "SLDSpectralEnergy", "IsDensity"), matrix);
    private static Formula Tensor(Formula left, Formula right) => At(Qualified("Matrix", "kronecker"), left, right);
    private static Formula MatrixOf(Formula space) => At(Qualified("Matrix"), space, space, Complexes());
    private static Formula Identity(Formula space) => Typed(D(1), MatrixOf(space));
    private static Formula Family(string outcomes, Formula space) => Arrow(X(outcomes), MatrixOf(space));
    private static Formula TensorSpace(string left, string right) => Product(X(left), X(right));
    private static Formula Product(Formula left, Formula right) => Parenthesized(Seq(left, Sp, Times, Sp, right));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body)));
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Arrow(Formula left, Formula right) => new Formula.TypeArrow(Parenthesized(left), Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula X(string name) => name switch { "ρ" => Rho, "σ" => SigmaLower, _ => F.Id(name) };
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "QuantumChannels",
        "AncillaFreeTesterRobustnessEquality", name);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
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
}
