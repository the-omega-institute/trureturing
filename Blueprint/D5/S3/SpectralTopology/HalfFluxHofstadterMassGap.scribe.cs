using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.SpectralTopology;

internal sealed class HalfFluxHofstadterMassGapDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/SpectralTopology/HalfFluxHofstadterMassGap";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/StatisticalMechanics/fabbrimarcelligiuliani2026conductivity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The third and fourth Hofstadter bands have a uniform gap at Fermi energy two for every nonzero mass in the interval from minus two to two.",
        H("The mass gap of the four Hofstadter bands"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bloch"),
                DeclarationHandle.Create(Module + ".bloch"),
                H("The Bloch Hamiltonian"),
                StatementSource.FromAuthor(Disp(BlochFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "This is the complex four-by-four Bloch matrix of the pi/2-flux Hofstadter model, "
                    + "with its overall minus sign. The real momenta k₁ and k₂ are unrestricted, "
                    + "and the real mass m enters through d = 2 + m. Each real quantity in a complex "
                    + "entry is included by Complex.ofReal. The matrix is equation "
                    + "Hofst_Hamiltonian in the source, TeX lines 663–671; the mass substitution "
                    + "is at lines 686–687."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bloch-is-hermitian"),
                DeclarationHandle.Create(Module + ".bloch_isHermitian"),
                H("Hermiticity for all real parameters"),
                StatementSource.FromAuthor(Disp(OverParameters(
                    At(Qualified("Matrix", "IsHermitian"), Bloch())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The diagonal entries are real, and opposite off-diagonal entries are complex "
                    + "conjugates. For real k, conjugating exp(2ik) gives exp(−2ik), and conjugating "
                    + "the latter gives exp(2ik). Checking the sixteen entries therefore identifies "
                    + "the conjugate transpose with the original matrix. No restriction on the mass "
                    + "or the momenta is needed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("band"),
                DeclarationHandle.Create(Module + ".band"),
                H("The energy bands in increasing order"),
                StatementSource.FromAuthor(Disp(BandFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The index j belongs to Fin 4, so j = 0, 1, 2, 3 names the source's first, "
                    + "second, third and fourth bands. Matrix.IsHermitian.eigenvalues₀ lists the "
                    + "real eigenvalues in decreasing order; Fin.rev reverses the index to obtain "
                    + "increasing order, retaining multiplicity. This expresses the convention "
                    + "for energy bands at TeX line 354."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fermi-energy"),
                DeclarationHandle.Create(Module + ".fermiEnergy"),
                H("The Fermi energy"),
                StatementSource.FromAuthor(Disp(Equal(Typed(Local("fermiEnergy"), Reals),
                    Band(FermiCoordinate, FermiCoordinate, RealNumber(0), Index(2))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The Fermi energy is the third band at zero mass and at the Fermi point "
                    + "(π/4, π/4). The point is specified at TeX line 674, and the energy is "
                    + "defined at lines 686–687. Its equality with the fourth band at that point "
                    + "is a separate part of the gap assertion."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("A uniform gap at every nonzero allowed mass"),
                StatementSource.FromAuthor(Disp(Equivalence(Local("claim"), GapStatement()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "At zero mass the fourth band at the Fermi point equals the Fermi energy. "
                    + "For each m with −2 ≤ m ≤ 2 and m ≠ 0, one positive real δ separates "
                    + "the fourth band above that energy and the third band below it, simultaneously "
                    + "for every pair of real momenta. The bound may depend on m but not on the "
                    + "momenta. This is the uniform inequality form of the question at TeX lines "
                    + "689–690. It quantifies over all real momenta, without taking extrema or "
                    + "requiring a choice of fundamental domain."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("A positive gap of at least m squared over five hundred"),
                StatementSource.FromAuthor(Disp(GapStatement())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "First put d = 2 + m and consider the real expression "
                        + "q = (y₁ − d)² + (y₂ − d)² + 2 − d², where y₁ ≤ 1 and y₂ ≤ 1. "
                        + "If m ≥ −2, then d ≥ 0. For d ≤ 1, the two squares give "
                        + "q ≥ 2 − d² ≥ (d − 2)²/2. For d > 1, each square is at least "
                        + "(d − 1)², so q ≥ 2(d − 1)² + 2 − d² = (d − 2)². "
                        + "Thus q ≥ m²/2 in both cases.")),
                    Paragraph(Text(
                        "Set z₁ = exp(2ik₁), z₂ = exp(2ik₂), y₁ = Im z₁ and y₂ = Im z₂. "
                        + "The phases have norm one, hence y₁ ≤ 1 and y₂ ≤ 1. Write H for the "
                        + "Bloch matrix and K = H − 2I. Permuting coordinates into the order "
                        + "(1,4,2,3) gives a block matrix with upper-left block "
                        + "A = diag(−d − 2, d − 2), lower-right block −2I₂, and upper-right block "
                        + "B whose rows are (−1 + iz₁, −1 + iz₂) and "
                        + "(−i − conjugate(z₂), −1 + i conjugate(z₁)).")),
                    Paragraph(Text(
                        "The Schur matrix S = A + BBᴴ/2 has diagonal entries s − d and d − s, "
                        + "where s = y₁ + y₂, and upper-right entry "
                        + "t = (1 − i)(1 − z₁ + z₂ + z₁z₂)/2; its lower-left entry is the "
                        + "conjugate of t. The unit-circle equations for z₁ and z₂ give "
                        + "|t|² = 2(1 − y₁y₂), so det S = −q. The lower triangular block matrix "
                        + "P with diagonal blocks I₂ and lower-left block Bᴴ/2 has determinant one, "
                        + "and PᴴKP = diag(S, −2I₂) in the permuted coordinates. Taking determinants "
                        + "gives det K = −4q. Consequently q > 0 whenever m ≥ −2 and m ≠ 0. "
                        + "Adding the scalar matrix −2I subtracts two from each ordered eigenvalue "
                        + "without changing its position.")),
                    Paragraph(Text(
                        "The Hermitian two-by-two matrix S has negative determinant, so the "
                        + "product of its two real eigenvalues is negative. Exactly one of them "
                        + "is positive. Factoring the characteristic polynomial of diag(S, −2I₂) "
                        + "shows that this block matrix also has exactly one positive eigenvalue. "
                        + "Inertia is preserved by the invertible congruence P and by the coordinate "
                        + "permutation, so K has positive index one. Its nonzero determinant gives "
                        + "rank four, and the sum of the positive and negative indices equals the "
                        + "rank. The negative index is therefore three.")),
                    Paragraph(Text(
                        "For −2 ≤ m ≤ 2, one has |d| ≤ 4. Every off-diagonal entry of K "
                        + "has norm at most two, and the diagonal estimates give a row sum of norms "
                        + "at most ten. Gershgorin's theorem places every eigenvalue in a disk "
                        + "centered at a diagonal entry with radius the sum of the other entry "
                        + "norms in that row. The triangle inequality therefore bounds the absolute "
                        + "value of every eigenvalue of K by ten.")),
                    Paragraph(Text(
                        "At k₁ = k₂ = π/4 and m = 0 the positive phases equal i and the negative "
                        + "phases equal −i. Substitution gives the characteristic polynomial "
                        + "X(X + 4)(X − 2)². Its complex roots, with multiplicity, are 2, 2, 0 "
                        + "and −4. Sorting their real parts identifies both the third and fourth "
                        + "bands with two; in particular the Fermi energy is two.")),
                    Paragraph(Text(
                        "Now take m ≥ −2 with m ≠ 0. In decreasing order, the top eigenvalue "
                        + "of K is positive: otherwise all four would be nonpositive, contradicting "
                        + "positive index one. Its second eigenvalue is negative: otherwise only "
                        + "the last two could be negative, contradicting negative index three. "
                        + "Reversing the indices and adding two gives band k₁ k₂ m 2 < 2 and "
                        + "2 < band k₁ k₂ m 3.")),
                    Paragraph(Text(
                        "Finally, det K = −4q and q ≥ m²/2 imply |det K| ≥ 2m². The absolute "
                        + "determinant is the product of the four absolute eigenvalues. After "
                        + "singling out any one eigenvalue, the other three factors have product "
                        + "at most 10³ = 1000. Hence every band satisfies "
                        + "|band k₁ k₂ m j − 2| ≥ m²/500. Choose δ = m²/500, which is positive "
                        + "for nonzero m. The strict signs of the third and fourth bands remove "
                        + "the absolute values in the two required directions. Replacing two "
                        + "by the Fermi energy proves both uniform inequalities, together with "
                        + "the equality at zero mass."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("fabbri-marcelli-giuliani-2026-half-flux-hofstadter-mass-gap"),
                    ResolutionKind.Proved)))));

    private static Formula BlochFormula()
    {
        Formula d = ComplexOfReal(Add(RealNumber(2), X("m")));
        Formula matrix = Seq(Begin, Grp(F.Id("pmatrix")),
            d, Amp, Subtract(ComplexNumber(1), Multiply(ImaginaryUnit, Phase(X("k₁")))), Amp,
            Subtract(ComplexNumber(1), Multiply(ImaginaryUnit, Phase(X("k₂")))), Amp, ComplexNumber(0), RowBreak,
            Add(ComplexNumber(1), Multiply(ImaginaryUnit, Phase(X("k₁"), negative: true))), Amp,
            ComplexNumber(0), Amp, ComplexNumber(0), Amp, Add(Negate(ImaginaryUnit), Phase(X("k₂"))), RowBreak,
            Add(ComplexNumber(1), Multiply(ImaginaryUnit, Phase(X("k₂"), negative: true))), Amp,
            ComplexNumber(0), Amp, ComplexNumber(0), Amp, Add(ComplexNumber(1), Multiply(ImaginaryUnit, Phase(X("k₁")))), RowBreak,
            ComplexNumber(0), Amp, Add(ImaginaryUnit, Phase(X("k₂"), negative: true)), Amp,
            Subtract(ComplexNumber(1), Multiply(ImaginaryUnit, Phase(X("k₁"), negative: true))), Amp, Negate(d),
            End, Grp(F.Id("pmatrix")));
        return OverParameters(Equal(Typed(Bloch(), MatrixType), Negate(matrix)));
    }

    private static Formula BandFormula() => OverParameters(All("j", FinFour,
        Equal(Typed(Band(X("k₁"), X("k₂"), X("m"), X("j")), Reals),
            At(new Formula.Subscript(Qualified("Matrix", "IsHermitian", "eigenvalues"), D(0)),
                At(Local("bloch_isHermitian"), X("k₁"), X("k₂"), X("m")),
                At(Qualified("Fin", "rev"), X("j"))))));

    private static Formula GapStatement()
    {
        Formula touching = Equal(Band(FermiCoordinate, FermiCoordinate, RealNumber(0), Index(3)), Local("fermiEnergy"));
        Formula separation = Conjunction(
            LE(Add(Local("fermiEnergy"), X("δ")), Band(X("k₁"), X("k₂"), X("m"), Index(3))),
            LE(Band(X("k₁"), X("k₂"), X("m"), Index(2)), Subtract(Local("fermiEnergy"), X("δ"))));
        Formula uniform = All("k₁", Reals, All("k₂", Reals, separation));
        Formula positiveGap = Some("δ", Reals, Conjunction(LT(RealNumber(0), X("δ")), uniform));
        Formula masses = All("m", Reals, Arrow(LE(Negate(RealNumber(2)), X("m")),
            Arrow(LE(X("m"), RealNumber(2)), Arrow(NotEqual(X("m"), RealNumber(0)), positiveGap))));
        return Conjunction(touching, masses);
    }

    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinFour => At(Qualified("Fin"), D(4));
    private static Formula MatrixType => At(Qualified("Matrix"), FinFour, FinFour, Complexes);
    private static Formula ImaginaryUnit => Qualified("Complex", "I");
    private static Formula FermiCoordinate => new Formula.Fraction(Qualified("Real", "pi"), RealNumber(4));
    private static Formula RealNumber(byte n) => Typed(D(n), Reals);
    private static Formula ComplexNumber(byte n) => Typed(D(n), Complexes);
    private static Formula Index(byte n) => Typed(D(n), FinFour);
    private static Formula ComplexOfReal(Formula value) => At(Qualified("Complex", "ofReal"), value);
    private static Formula Phase(Formula k, bool negative = false) => At(Qualified("Complex", "exp"),
        Multiply(Multiply(negative ? Negate(ComplexNumber(2)) : ComplexNumber(2), ImaginaryUnit), ComplexOfReal(k)));
    private static Formula Bloch() => At(Local("bloch"), X("k₁"), X("k₂"), X("m"));
    private static Formula Band(Formula k1, Formula k2, Formula m, Formula j) => At(Local("band"), k1, k2, m, j);
    private static Formula OverParameters(Formula body) => All("k₁", Reals, All("k₂", Reals, All("m", Reals, body)));
    private static Formula Local(string name) => Qualified("D5", "S3", "SpectralTopology", "HalfFluxHofstadterMassGap", name);
    private static Formula X(string name) => name switch
    {
        "k₁" => new Formula.Subscript(F.Id("k"), D(1)),
        "k₂" => new Formula.Subscript(F.Id("k"), D(2)),
        "δ" => DeltaLower,
        _ => F.Id(name),
    };
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            if (part == "bloch_isHermitian")
                items.Add(new Formula.Subscript(F.Id("bloch"), F.Id("isHermitian")));
            else
                items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Negate(Formula value) => new Formula.Negate(Parenthesized(value));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LT(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
