using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Thermal;

internal sealed class MetrotropyHalfErgotropyRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Thermal/MetrotropyHalfErgotropyRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create(
        "D5/L/HilbertOperators/solfanellibuffonicuccolicampisi2019metrotropy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A non-stationary pure state in dimension four has metrotropy strictly greater than half its ergotropy.",
        H("Metrotropy can exceed half the ergotropy"),
        Blocks(
            Node("measured", "A nonselective rank-one measurement", MeasuredFormula(),
                "The columns of a unitary u form an orthonormal basis. For each column, take its rank-one orthogonal projector. "
                    + "The measured matrix is the sum of the products of each projector, the input matrix, and the same projector. "
                    + "This is the nonselective measurement of Metrotropy02.tex, lines 164–175. The definition applies to every complex input matrix and every natural dimension, without a density assumption.",
                AssessedProvenance.FromLiterature(Source)),
            Node("metrotropy", "Energy extractable by a rank-one measurement", MetrotropyFormula(),
                "Subtract the infimum of the energies after rank-one projective measurements from the initial energy. "
                    + "The real energy expect of a matrix and a Hamiltonian is the real part of the trace of their product, with the Hamiltonian on the left. "
                    + "Every orthonormal measurement basis is represented by the columns of a unitary. "
                    + "Metrotropy02.tex, line 272, defines metrotropy as initial energy minus minimum final energy; lines 298–304 give the non-stationary measurement setting. "
                    + "The displayed definition uses the real infimum and is defined even for matrices that are not states or Hamiltonians.",
                AssessedProvenance.FromLiterature(Source)),
            Node("ergotropy", "Energy extractable by a unitary", ErgotropyFormula(),
                "Subtract the infimum of the energies of all unitary conjugates of the input matrix from its initial energy. "
                    + "Subtype.val explicitly extracts the complex matrix underlying v, and unitaryEvolution sends the input to that matrix times the input times its conjugate transpose. "
                    + "This is the unitary optimization of Metrotropy02.tex, lines 130–153 and 291–296, expressed with a real infimum. "
                    + "The definition itself imposes neither Hermiticity nor positivity nor trace normalization.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The proposed inequality for non-stationary states", ClaimFormula(),
                "For every natural dimension d, Hermitian matrix h, and density matrix ρ that does not commute with h, "
                    + "the proposed inequality bounds the metrotropy by one half of the ergotropy. A density matrix here is positive semidefinite with complex trace one. "
                    + "Metrotropy02.tex, line 308, asks whether this inequality holds when the initial state is not stationary. "
                    + "The universal proposition displayed here gives that question precise matrix domains and quantifiers; measurements have rank-one projectors.",
                AssessedProvenance.FromRepo(Source)),
            Node("u4", "The normalized four-dimensional Walsh matrix", UFourFormula(),
                "The four rows are the real Walsh vectors, each scaled by one half. "
                    + "This matrix supplies the measurement basis of the four-dimensional counterexample.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("metrotropy-half-ergotropy-u4-unitary"),
                DeclarationHandle.Create(Prefix + "u4_unitary"),
                H("The Walsh matrix is unitary"),
                StatementSource.FromAuthor(Disp(new Formula.Relation(Local("u4"),
                    FormulaRelationOperator.MemberOf,
                    At(Qualified("Matrix", "unitaryGroup"), FinOf(D(4)), Complexes())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The product of this matrix with its conjugate transpose is the identity. "
                        + "Its rows and columns therefore form orthonormal bases of complex four-space."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("metrotropy-half-ergotropy-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A four-dimensional counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take the Hamiltonian H = diag(0, 1, 2, 10), the vector ψ = (0, 0, 3i/5, 4/5), and the pure state ρ = ψψ†. "
                            + "Let U be one half of the real matrix with successive rows (1, 1, 1, 1), (1, −1, 1, −1), (1, 1, −1, −1), and (1, −1, −1, 1). "
                            + "The trace of ρ is 9/25 + 16/25 = 1, and ρ is positive semidefinite as an outer product. The real diagonal H is Hermitian. "
                            + "With coordinates numbered from zero, the (2, 3) entry of Hρ − ρH is −96i/25, so H and ρ do not commute. "
                            + "Multiplying U by its conjugate transpose gives the identity, so U is unitary.")),
                    Paragraph(Text(
                        "For an arbitrary unitary u, write the nonselective measurement as the sum of its rank-one projectors multiplied on both sides of the input. "
                            + "For a pure input ψψ†, multiplication of outer products expresses each summand as the projector onto column k multiplied by "
                            + "the product of the inner product of that column with ψ and its complex conjugate. "
                            + "For the chosen U and ψ, this product is 1/4 for each of the four columns. "
                            + "The column projectors sum to the identity, so the measured state is I/4. "
                            + "Direct evaluation gives initial energy 2(9/25) + 10(16/25) = 178/25 and measured energy (0 + 1 + 2 + 10)/4 = 13/4.")),
                    Paragraph(Text(
                        "If a diagonal Hamiltonian has nonnegative real diagonal entries and a matrix σ is positive semidefinite, then the energy of σ is nonnegative. "
                            + "Indeed, the diagonal entries of σ are real and nonnegative, and the real part of the trace of the product is the sum of their products with the Hamiltonian entries. "
                            + "Every measured output of ρ is positive semidefinite, since it is a sum of Kraus products of a positive semidefinite matrix. "
                            + "Thus the set of measurement energies is bounded below by zero. Its infimum is at most the energy 13/4 attained by U. "
                            + "Subtracting from 178/25 gives metrotropy at least 387/100.")),
                    Paragraph(Text(
                        "The set of unitary output energies is nonempty because it contains the output of the identity unitary. "
                            + "Unitary conjugation preserves positive semidefiniteness, so the same diagonal-energy argument makes every element of this set nonnegative. "
                            + "Its infimum is therefore nonnegative, giving ergotropy at most 178/25. "
                            + "Half the ergotropy is consequently at most 89/25 = 356/100, strictly below the metrotropy lower bound 387/100. "
                            + "Applying the universal inequality to dimension four, H, and ρ would contradict these bounds; hence the proposition is false."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("solfanelli-buffoni-cuccoli-campisi-2019-metrotropy-half-ergotropy"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("metrotropy-half-ergotropy-" + name),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] names)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var name in names)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(name));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) => Qualified(
        "D5", "S3", "Quantum", "Thermal", "MetrotropyHalfErgotropyRefutation", name);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(X("C")));
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);
    private static Formula MatrixType() => At(Qualified("Matrix"), FinOf(X("d")), FinOf(X("d")), Complexes());
    private static Formula Unitaries() => At(Qualified("Matrix", "unitaryGroup"), FinOf(X("d")), Complexes());
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Eq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Ne(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Product(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Energy(Formula state, Formula hamiltonian) => At(Qualified(
        "D5", "S3", "Quantum", "Entanglement", "GHZMeasureBiseparableBound", "expect"), state, hamiltonian);
    private static Formula EnergySet(Formula basis, Formula output) => Seq(
        OpenBrace, X("e"), Colon, Sp, Reals(), Sp, Mid, Sp,
        Some(basis, Unitaries(), Eq(X("e"), Energy(output, X("h")))), CloseBrace);
    private static Formula EnergyBinders(Formula body) => All(X("d"), Naturals(),
        All(X("h"), MatrixType(), All(Rho, MatrixType(), body)));

    private static Formula UFourFormula()
    {
        Formula one = Typed(D(1), Complexes());
        Formula minusOne = new Formula.Negate(one);
        Formula matrix = Seq(Begin, Grp(X("bmatrix")),
            one, Amp, one, Amp, one, Amp, one, RowBreak,
            one, Amp, minusOne, Amp, one, Amp, minusOne, RowBreak,
            one, Amp, one, Amp, minusOne, Amp, minusOne, RowBreak,
            one, Amp, minusOne, Amp, minusOne, Amp, one, End, Grp(X("bmatrix")));
        return Eq(Typed(Local("u4"),
                At(Qualified("Matrix"), FinOf(D(4)), FinOf(D(4)), Complexes())),
            Seq(Parenthesized(new Formula.Fraction(one, Typed(D(2), Complexes()))),
                Sp, Cdot, Sp, Parenthesized(matrix)));
    }

    private static Formula MeasuredFormula() => All(X("d"), Naturals(),
        All(X("u"), Unitaries(), All(Rho, MatrixType(), Eq(LocalCall("measured", X("u"), Rho),
            At(Qualified("D5", "S3", "Quantum", "QuantumChannels", "OutputMaximalCoherenceTensorizationRefutation", "krausApply"),
                At(Qualified("D5", "S3", "Quantum", "Decoherence", "DephasingTwoClassicalityBlockRefutation", "measurementProjector"), X("u")), Rho)))));

    private static Formula MetrotropyFormula() => EnergyBinders(Eq(LocalCall("metrotropy", X("h"), Rho),
        Subtract(Energy(Rho, X("h")), At(Qualified("sInf"),
            EnergySet(X("u"), LocalCall("measured", X("u"), Rho))))));

    private static Formula ErgotropyFormula() => EnergyBinders(Eq(LocalCall("ergotropy", X("h"), Rho),
        Subtract(Energy(Rho, X("h")), At(Qualified("sInf"),
            EnergySet(X("v"), At(Qualified("D5", "S3", "Quantum", "Decoherence", "ProjectedUnistochasticDynamics", "unitaryEvolution"),
                Typed(At(Qualified("Subtype", "val"), X("v")), MatrixType()), Rho))))));

    private static Formula ClaimFormula() => IffOf(Local("claim"), EnergyBinders(
        Imp(At(Qualified("Matrix", "IsHermitian"), X("h")),
            Imp(At(Qualified("D5", "S3", "Quantum", "Information", "SLDSpectralEnergy", "IsDensity"), Rho),
                Imp(Ne(Product(X("h"), Rho), Product(Rho, X("h"))),
                    LE(LocalCall("metrotropy", X("h"), Rho),
                        new Formula.Fraction(LocalCall("ergotropy", X("h"), Rho), Typed(D(2), Reals()))))))));
}
