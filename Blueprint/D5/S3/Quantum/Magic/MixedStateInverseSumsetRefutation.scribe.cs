using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Magic;

internal sealed class MixedStateInverseSumsetRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Divergence/bugujaffe2025ruzsa");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The equal mixture of two levels in dimension seven violates the proposed mixed-state quantum inverse sumset bound.",
        H("A mixed-state counterexample to the quantum inverse sumset bound"),
        Blocks(
            Definition("weyl", "The clock-first Weyl operator", WeylFormula(),
                "For a nonzero natural dimension d, the clock-first Weyl operator multiplies the clock power by the shift power and the phase shown above. "
                    + "The exponents use the natural representatives ZMod.val; the phase exponent first negates the product in ZMod d. "
                    + "The division (d + 1)/2 is natural-number division. This is the source's odd-dimensional convention in IEEE_Final_BGJ.tex, lines 726–750. "
                    + "The formula is defined for every nonzero d; the source uses its odd-prime specialization and gives a separate phase convention for d = 2.", Lit()),
            Definition("charFun", "The characteristic function", CharFunFormula(),
                "The characteristic function is the trace pairing with the Weyl operator at the negative phase-space point. "
                    + "Here x is a pair of residues and its two projections are negated separately. "
                    + "This is the single-qudit characteristic function of IEEE_Final_BGJ.tex, lines 760–773, extended to arbitrary complex matrices.", Lit()),
            Definition("meanState", "The mean-state operator", MeanStateFormula(),
                "Retain precisely the characteristic coefficients of norm one, reconstruct their Weyl expansion, and divide by the dimension, cast to the complex scalars. "
                    + "The sum ranges over all phase-space points satisfying that norm condition. "
                    + "This combines the reconstruction formula in IEEE_Final_BGJ.tex, lines 767–773, with the mean state in lines 842–856. "
                    + "The displayed operator formula applies to arbitrary matrices, without assuming positivity or trace one.", Lit()),
            Definition("meanRank", "The rank of the mean state", MeanRankFormula(),
                "The natural-valued matrix rank of the mean-state operator is the quantity R of IEEE_Final_BGJ.tex, line 1000.", Lit()),
            Definition("magicGap", "The magic gap and its empty-set convention", MagicGapFormula(),
                "The finite set a contains the nonzero characteristic coefficients whose norm is different from one. "
                    + "If this set is nonempty, subtract its largest coefficient norm from one; if it is empty, assign zero. "
                    + "The finite maximum is Finset.sup' on its nonempty branch. This is the convention of IEEE_Final_BGJ.tex, lines 870–876.", Lit()),
            Definition("gapFactor", "The squared gap factor", GapFactorFormula(),
                "The factor lambda is the square of one minus the magic gap, as in the inverse sumset bound of IEEE_Final_BGJ.tex, lines 2026–2037, and its mixed-state expectation in lines 2101–2108.", Lit()),
            Definition("purity", "The real trace of the square", PurityFormula(),
                "The purity expression takes the real part of the trace of the matrix square. For density matrices this is the purity factor in equation (58), IEEE_Final_BGJ.tex, lines 2101–2108. "
                    + "The definition also assigns a real value to an arbitrary complex matrix.", Lit()),
            Definition("convolution", "Quantum convolution by a linear permutation", ConvolutionFormula(),
                "The matrix u sends the basis pair (i,j) to (si + tj, −ti + sj). Conjugate the tensor product by u and take the partial trace over the right factor. "
                    + "For nonzero s and t satisfying s squared plus t squared equal to one, u is the unitary of IEEE_Final_BGJ.tex, lines 885–896. "
                    + "The displayed matrix formula is defined without imposing those parameter conditions or density assumptions on its arguments.", Lit()),
            Definition("claim", "The mixed-state inverse sumset expectation", ClaimFormula(),
                "This is a single-qudit formulation of the expected mixed-state inequality (58) in Remark 45, IEEE_Final_BGJ.tex, lines 2101–2123. "
                    + "The dimension is prime and nonzero, and s and t are nonzero residues with s squared plus t squared equal to one. "
                    + "The density states σ and τ represent the mean state of ρ and its self-convolution through the stated equalities in CStarMatrix. "
                    + "Each density state is a positive semidefinite complex matrix of trace one. The notation Subtype.val extracts that matrix. "
                    + "The real number δ is the quantum-doubling constant of lines 1982–1994; r is the mean-state rank cast from the naturals to the reals, and l is the squared gap factor. "
                    + "For every real c with 1 < δ ≤ c, the proposed relative-entropy upper bound is required whenever the logarithm argument and the denominator are both positive. "
                    + "The entropy and relative entropy use natural logarithms.", Repo()),
            Describe.Lean(
                DescribeId.Create("mixed-state-inverse-sumset-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The seven-dimensional counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                Repo(),
                Blocks(
                    Paragraph(Text(
                        "In dimension seven, let ρ be diagonal with weights 1/2 at levels 0 and 1 and zero elsewhere. "
                            + "Let σ be the identity matrix divided by seven, and let τ be diagonal with weights 1/4, 1/2 and 1/4 at levels 0, 2 and 4. "
                            + "Their diagonal entries are nonnegative and sum to one, so all three are density states.")),
                    Paragraph(Text(
                        "Set s = t = 2 in ZMod 7. The convolution matrix sends (i,j) to (2i + 2j, −2i + 2j). "
                            + "The diagonal tensor product has four equally weighted input pairs (0,0), (0,1), (1,0) and (1,1), whose left outputs are respectively 0, 2, 2 and 4. "
                            + "Expanding matrix multiplication and the right partial trace over the seven residues therefore gives ρ convolved with itself equal to τ. "
                            + "The logarithm of a diagonal matrix is diagonal with the scalar logarithms of its entries. "
                            + "Consequently the entropy of ρ is log 2, and the entropy of τ is (3/2) log 2; zero entries contribute zero.")),
                    Paragraph(Text(
                        "The diagonal entry of the Weyl operator at (p,q) vanishes unless q = 0. "
                            + "When q = 0, its entry at i is windowRoot(7) to the power val(i) val(p). "
                            + "Thus the characteristic function of ρ vanishes off the q = 0 axis and equals (1 + windowRoot(7) to the power val(−p))/2 on that axis. "
                            + "Every power of this primitive seventh root has norm one. Equality in the triangle inequality forces the characteristic-function norm to equal one only when that power is one. "
                            + "Primitivity and the natural representative val(−p) < 7 then force p = 0. "
                            + "Conversely the coefficient at (0,0) equals one. The triangle inequality also bounds every characteristic-function norm by one.")),
                    Paragraph(Text(
                        "Only the coefficient at (0,0) therefore remains in the mean-state expansion, giving σ. "
                            + "All seven diagonal entries of σ are nonzero, so its rank is seven. "
                            + "If the finite set defining the magic gap is nonempty, its maximum norm lies between zero and one; if it is empty, the gap is zero. "
                            + "In either case l = gapFactor(ρ) satisfies 0 ≤ l ≤ 1. Direct diagonal multiplication gives purity(ρ) = 1/2. "
                            + "The logarithm of σ is the identity matrix multiplied by −log 7. "
                            + "Writing relative entropy as minus the entropy minus the trace against that logarithm gives D(ρ ∥ σ) = log 7 − log 2.")),
                    Paragraph(Text(
                        "The entropy difference gives δ = exp((1/2) log 2) > 1. Choose c equal to this value. "
                            + "For every real l between zero and one, the argument A = 1 + l(7/2 − 1) lies in [1,7/2]. "
                            + "Monotonicity of the logarithm gives log 7 − log A ≥ log 2 > 0. "
                            + "The proposed right side is consequently at most (log 7/log 2)((1/2) log 2) = (1/2) log 7. "
                            + "On the other hand, 4 < 7 implies 2 log 2 < log 7, hence (1/2) log 7 < log 7 − log 2.")),
                    Paragraph(Text(
                        "Seven is prime, both convolution parameters are nonzero, and 2 squared plus 2 squared equals one in ZMod 7. "
                            + "The computed mean state and convolution supply the two required matrix equalities, and the bounds on A supply both positivity hypotheses. "
                            + "Applying the proposed universal inequality to these density states and c would put log 7 − log 2 at most (1/2) log 7, contradicting the strict inequality above."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bu-gu-jaffe-2025-mixed-state-inverse-sumset"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Definition(string name, string title, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("mixed-state-inverse-sumset-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static AssessedProvenance Lit() => AssessedProvenance.FromLiterature(Source);
    private static AssessedProvenance Repo() => AssessedProvenance.FromRepo(Source);

    private static Formula WeylFormula()
    {
        Formula phase = Pow(Pow(Window("windowRoot", X("d")),
            At(Qualified("Nat", "div"), Add(X("d"), D(1)), D(2))),
            Val(new Formula.Negate(Multiply(X("p"), X("q")))));
        Formula word = Multiply(Pow(Window("clockMatrix", X("d")), Val(X("p"))),
            Pow(Window("shiftMatrix", X("d")), Val(X("q"))));
        return Dimension(All("p", Residues(), All("q", Residues(),
            Equal(Typed(LocalCall("weyl", X("d"), X("p"), X("q")), Mat()), Smul(phase, word)))));
    }

    private static Formula CharFunFormula() => Operators(All("x", PhaseSpace(),
        Equal(Typed(LocalCall("charFun", X("ρ"), X("x")), Complexes()),
            At(Qualified("Matrix", "trace"), Multiply(X("ρ"),
                LocalCall("weyl", X("d"), new Formula.Negate(First(X("x"))),
                    new Formula.Negate(Second(X("x")))))))));

    private static Formula MeanStateFormula()
    {
        Formula selected = At(Qualified("Finset", "filter"),
            LambdaOf("x", PhaseSpace(), Equal(Norm(LocalCall("charFun", X("ρ"), X("x"))), Typed(D(1), Reals()))),
            Typed(Qualified("Finset", "univ"), FinsetOf(PhaseSpace())));
        Formula expansion = At(Qualified("Finset", "sum"), selected,
            LambdaOf("x", PhaseSpace(), Smul(LocalCall("charFun", X("ρ"), X("x")),
                LocalCall("weyl", X("d"), First(X("x")), Second(X("x"))))));
        return Operators(Equal(Typed(LocalCall("meanState", X("ρ")), Mat()),
            Smul(At(Qualified("Inv", "inv"), CastNat(X("d"), Complexes())), expansion)));
    }

    private static Formula MeanRankFormula() => Operators(Equal(
        Typed(LocalCall("meanRank", X("ρ")), Naturals()),
        At(Qualified("Matrix", "rank"), LocalCall("meanState", X("ρ")))));

    private static Formula MagicGapFormula()
    {
        Formula selected = At(Qualified("Finset", "filter"), LambdaOf("x", PhaseSpace(),
            And(NotEqual(LocalCall("charFun", X("ρ"), X("x")), Typed(D(0), Complexes())),
                NotEqual(Norm(LocalCall("charFun", X("ρ"), X("x"))), Typed(D(1), Reals())))),
            Typed(Qualified("Finset", "univ"), FinsetOf(PhaseSpace())));
        Formula maximum = Seq(new Formula.Subscript(Max, Member(X("x"), X("a"))), Sp,
            Norm(LocalCall("charFun", X("ρ"), X("x"))));
        return Operators(Let("a", FinsetOf(PhaseSpace()), selected,
            Equal(Typed(LocalCall("magicGap", X("ρ")), Reals()),
                At(Qualified("ite"), At(Qualified("Finset", "Nonempty"), X("a")),
                    Subtract(Typed(D(1), Reals()), maximum), Typed(D(0), Reals())))));
    }

    private static Formula GapFactorFormula() => Operators(Equal(
        Typed(LocalCall("gapFactor", X("ρ")), Reals()),
        Pow(Parenthesized(Subtract(Typed(D(1), Reals()), LocalCall("magicGap", X("ρ")))), D(2))));

    private static Formula PurityFormula() => Operators(Equal(
        Typed(LocalCall("purity", X("ρ")), Reals()),
        At(Qualified("Complex", "re"), At(Qualified("Matrix", "trace"), Multiply(X("ρ"), X("ρ"))))));

    private static Formula ConvolutionFormula()
    {
        Formula image = Pair(Add(Multiply(X("s"), First(X("b"))), Multiply(X("t"), Second(X("b")))),
            Add(Multiply(new Formula.Negate(X("t")), First(X("b"))), Multiply(X("s"), Second(X("b")))));
        Formula u = LambdaOf("a", PhaseSpace(), LambdaOf("b", PhaseSpace(),
            At(Qualified("ite"), Equal(X("a"), image), Typed(D(1), Complexes()), Typed(D(0), Complexes()))));
        Formula tensor = At(Qualified("Matrix", "kroneckerMap"),
            LambdaOf("x1", Complexes(), LambdaOf("x2", Complexes(), Multiply(X("x1"), X("x2")))), X("ρ"), X("σ"));
        Formula product = Multiply(Multiply(X("u"), tensor), At(Qualified("Matrix", "conjTranspose"), X("u")));
        return Dimension(All("s", Residues(), All("t", Residues(), All("ρ", Mat(), All("σ", Mat(),
            Let("u", At(Qualified("Matrix"), PhaseSpace(), PhaseSpace(), Complexes()), u,
                Equal(Typed(LocalCall("convolution", X("s"), X("t"), X("ρ"), X("σ")), Mat()),
                    At(Qualified("D5", "S3", "Quantum", "Information", "PartialTraceMutualInformation", "partialTraceRight"), product))))))));
    }

    private static Formula ClaimFormula()
    {
        Formula matrix = Typed(At(Qualified("Subtype", "val"), X("ρ")), Mat());
        Formula argument = Add(Typed(D(1), Reals()), Multiply(X("l"), Parenthesized(
            Subtract(Multiply(X("r"), LocalCall("purity", matrix)), Typed(D(1), Reals())))));
        Formula denominator = Subtract(LogOf(X("r")), LogOf(argument));
        Formula bound = LE(At(Qualified("D5", "S3", "Quantum", "Divergence", "QuantumRelativeEntropyDefectComposition", "quantumRelativeEntropy"), X("ρ"), X("σ")),
            Multiply(new Formula.Fraction(LogOf(X("r")), denominator), LogOf(X("c"))));
        Formula inequalities = Imp(LT(Typed(D(1), Reals()), X("δ")), Imp(LE(X("δ"), X("c")),
            Imp(LT(Typed(D(0), Reals()), argument), Imp(LT(Typed(D(0), Reals()), denominator), bound))));
        Formula definitions = Let("δ", Reals(), At(Qualified("Real", "exp"),
            Subtract(Entropy(X("τ")), Entropy(X("ρ")))),
            Let("r", Reals(), CastNat(LocalCall("meanRank", matrix), Reals()),
                Let("l", Reals(), LocalCall("gapFactor", matrix), inequalities)));
        Formula stateEqualities = Imp(Equal(StateValue("σ"), At(Qualified("CStarMatrix", "ofMatrix"), LocalCall("meanState", matrix))),
            Imp(Equal(StateValue("τ"), At(Qualified("CStarMatrix", "ofMatrix"), LocalCall("convolution", X("s"), X("t"), matrix, matrix))), definitions));
        Formula states = All("ρ", Density(), All("σ", Density(), All("τ", Density(), All("c", Reals(), stateEqualities))));
        Formula parameters = All("s", Residues(), All("t", Residues(),
            Imp(NotEqual(X("s"), Typed(D(0), Residues())), Imp(NotEqual(X("t"), Typed(D(0), Residues())),
                Imp(Equal(Add(Pow(X("s"), D(2)), Pow(X("t"), D(2))), Typed(D(1), Residues())), states)))));
        return IffOf(Local("claim"), Dimension(Imp(At(Qualified("Nat", "Prime"), X("d")), parameters)));
    }

    private static Formula Operators(Formula body) => Dimension(All("ρ", Mat(), body));
    private static Formula Dimension(Formula body) =>
        Seq(Forall, Sp, Typed(X("d"), Naturals()), Sp,
            OpenBracket, At(Qualified("NeZero"), X("d")), CloseBracket, Comma, Sp,
            Parenthesized(body));
    private static Formula Mat() => At(Qualified("Matrix"), Residues(), Residues(), Complexes());
    private static Formula Residues() => At(Qualified("ZMod"), X("d"));
    private static Formula PhaseSpace() => Seq(Residues(), Sp, Times, Sp, Residues());
    private static Formula FinsetOf(Formula type) => At(Qualified("Finset"), type);
    private static Formula Density() => At(Qualified("D5", "S3", "Quantum", "Divergence", "QuantumRelativeEntropyDefectComposition", "DensityState"), Residues());
    private static Formula StateValue(string name) => Typed(At(Qualified("Subtype", "val"), X(name)),
        At(Qualified("CStarMatrix"), Residues(), Residues(), Complexes()));
    private static Formula Entropy(Formula state) => At(Qualified("D5", "S3", "Quantum", "Divergence", "VonNeumannEntropyPinching", "vonNeumannEntropy"), state);
    private static Formula LogOf(Formula value) => At(Qualified("Real", "log"), value);
    private static Formula CastNat(Formula value, Formula type) => Typed(At(Qualified("Nat", "cast"), value), type);
    private static Formula Val(Formula value) => At(Qualified("ZMod", "val"), value);
    private static Formula First(Formula value) => At(Qualified("Prod", "fst"), value);
    private static Formula Second(Formula value) => At(Qualified("Prod", "snd"), value);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Norm(Formula value) => new Formula.Norm(value);
    private static Formula Smul(Formula scalar, Formula matrix) => Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(matrix));
    private static Formula Window(string name, Formula d) => At(Qualified("D5", "S3", "Observer", "WindowRegister", name), d);
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Magic", "MixedStateInverseSumsetRefutation", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula X(string name) => name switch
    {
        "ρ" => Rho, "σ" => SigmaLower, "τ" => Tau, "δ" => DeltaLower, _ => F.Id(name),
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
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Let(string name, Formula type, Formula value, Formula body) =>
        Seq(Qualified("let"), Sp, Typed(X(name), type), Sp, Colon, Eq, Sp, value, Semi, Sp, Parenthesized(body));
    private static Formula Imp(Formula premise, Formula conclusion) =>
        new Formula.TypeArrow(Parenthesized(premise), Parenthesized(conclusion));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Member(Formula value, Formula set) => new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    private static Formula LT(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
}
