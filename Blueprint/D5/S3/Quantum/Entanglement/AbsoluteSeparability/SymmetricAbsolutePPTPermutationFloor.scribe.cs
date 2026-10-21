using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsoluteSeparability;

internal sealed class SymmetricAbsolutePPTPermutationFloorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumContext/louvet2025symmetricppt");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Permutation symmetrizers retain a positive floor under every site partial transpose.", H("A partial-transpose floor for symmetric tensors"), Blocks(
            Describe.Lean(DescribeId.Create("lsappt-issymmetricvector"), DeclarationHandle.Create(Prefix + "IsSymmetricVector"),
                H("Permutation invariant vectors"), StatementSource.FromAuthor(Disp(SymmetricDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The source states on p. 1: “They satisfy ρ = πρπ′ with π and π′ any pair of permutation operators.” A symmetric vector is fixed by every site permutation; the site and local-label sets here are arbitrary finite types."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lsappt-q"), DeclarationHandle.Create(Prefix + "Q"),
                H("Permutation matrices on words"), StatementSource.FromAuthor(Disp(PermutationDefinition())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The inverse site permutation reindexes functions. The associated permutation matrix sends v to the vector x mapped to v(x composed with sigma)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lsappt-p"), DeclarationHandle.Create(Prefix + "P"),
                H("Permutation symmetrizer"), StatementSource.FromAuthor(Disp(ProjectorDefinition())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Averaging the word permutation matrices gives the orthogonal projector onto symmetric vectors."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lsappt-local-localp"), DeclarationHandle.Create(Prefix + "localP"),
                H("Local symmetric projector"), StatementSource.FromAuthor(Disp(LocalDefinition())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The stabilizer of a site subset permutes that subset and its complement independently. Its average is the projector onto the tensor product of their symmetric subspaces."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lsappt-p-hermitian"), DeclarationHandle.Create(Prefix + "P_hermitian"),
                H("Hermitian symmetrizer"), StatementSource.FromAuthor(Disp(ProjectorHermitian())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Inversion permutes the summands of the adjoint average."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lsappt-p-idempotent"), DeclarationHandle.Create(Prefix + "P_idempotent"),
                H("Idempotent symmetrizer"), StatementSource.FromAuthor(Disp(ProjectorIdempotent())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Multiplying a finite group average by itself preserves it."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lsappt-p-mulvec-symmetric"), DeclarationHandle.Create(Prefix + "P_mulVec_symmetric"),
                H("Symmetric image"), StatementSource.FromAuthor(Disp(SymmetricRange())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The averaged vector is invariant under every site permutation."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lsappt-p-mulvec-of-symmetric"), DeclarationHandle.Create(Prefix + "P_mulVec_of_symmetric"),
                H("Fixed symmetric vectors"), StatementSource.FromAuthor(Disp(FixedVectors())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Every site permutation fixes a symmetric vector, so their average does as well."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lsappt-pis-hermitian"), DeclarationHandle.Create(Prefix + "PiS_hermitian"),
                H("Hermitian local projector"), StatementSource.FromAuthor(Disp(LocalHermitian())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The stabilizer average is Hermitian."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lsappt-pis-idempotent"), DeclarationHandle.Create(Prefix + "PiS_idempotent"),
                H("Idempotent local projector"), StatementSource.FromAuthor(Disp(LocalIdempotent())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The stabilizer average is idempotent."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lsappt-pis-psd"), DeclarationHandle.Create(Prefix + "PiS_psd"),
                H("Positive local projector"), StatementSource.FromAuthor(Disp(LocalPositive())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A Hermitian idempotent matrix is positive semidefinite."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lsappt-pis-mul-p"), DeclarationHandle.Create(Prefix + "PiS_mul_P"),
                H("Local support of the symmetrizer"), StatementSource.FromAuthor(Disp(LocalFixesGlobal())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A fully symmetric vector is symmetric on either side of any site partition."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lsappt-partialtranspose-pis-sandwich"), DeclarationHandle.Create(Prefix + "partialTranspose_PiS_sandwich"),
                H("Partial transpose of a local sandwich"), StatementSource.FromAuthor(Disp(TransposeSandwich())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The two local projectors are real symmetric. Their tensor product can pass through partial transposition on either side of a matrix."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lsappt-symmetrizer-partialtranspose-floor"), DeclarationHandle.Create(Prefix + "symmetrizer_partialTranspose_floor"),
                H("Positive floor after partial transpose"), StatementSource.FromAuthor(Disp(TransposeFloor())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The cosets of the subset stabilizer have representatives that exchange equally many sites across the partition. Each partially transposed representative is a Gram matrix. The identity representative supplies the displayed floor; all other contributions are positive."))), DescribeRole.Theorem))));

    private static Formula X(string name) => F.Id(name);
    private static Formula Q(params string[] names) => Seq(Operatorname,
        Grp(Seq([.. names.SelectMany((name, index) => index == 0
            ? new Formula[] { X(name) } : new Formula[] { Dot, X(name) })])));
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Arr(Formula left, Formula right) => new Formula.TypeArrow(left, right);
    private static Formula Eqn(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);


    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Ifff(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Minusf(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Timesf(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Pow(Formula left, Formula right) => new Formula.Power(Parenthesized(left), right);

    private static Formula Inv(Formula value) => Pow(value, new Formula.Negate(D(1)));

    private static Formula Complexes => Seq(Mathbb, Grp(X("C")));
    private static Formula Types => Q("Type");
    private static Formula Matrix(Formula index) => At(Q("Matrix"), index, index, Complexes);

    private static Formula Inst(string cls, Formula type) => Seq(OpenBracket, At(Q(cls), type), CloseBracket, Sp);
    private static Formula FiniteTypes(Formula body) => All("I", Types, All("L", Types,
        Seq(Inst("Fintype", X("I")), Inst("DecidableEq", X("I")), Inst("Fintype", X("L")), Inst("DecidableEq", X("L")), body)));
    private static Formula PermutationTypes(Formula body) => All("I", Types, All("L", Types,
        Seq(Inst("Fintype", X("I")), Inst("DecidableEq", X("I")), Inst("Fintype", X("L")), Inst("DecidableEq", X("L")), body)));
    private static Formula LocalTypes(Formula body) => All("I", Types,
        Seq(Inst("Fintype", X("I")), Inst("DecidableEq", X("I")), All("L", Types,
            Seq(Inst("Fintype", X("L")), Inst("DecidableEq", X("L")), body))));
    private static Formula Word => Arr(X("I"), X("L"));


    private static Formula Local(string owner, string name, params Formula[] args) => At(Q("D5", "S3", "Quantum", "Entanglement", "AbsoluteSeparability", owner, name), args);
    private static Formula PT(Formula s, Formula a) => Local("SymmetricAbsolutePPTPureBound", "partialTransposeOn", s, a);
    private static Formula PSD(Formula a) => At(Q("Matrix", "PosSemidef"), a);
    private static Formula Herm(Formula a) => At(Q("Matrix", "IsHermitian"), a);
    private static Formula MulVec(Formula a, Formula v) => At(Q("Matrix", "mulVec"), a, v);

    private static Formula Sym(Formula v) => Local("SymmetricAbsolutePPTPermutationFloor", "IsSymmetricVector", v);
    private static Formula Projector => Local("SymmetricAbsolutePPTPermutationFloor", "P", X("I"), X("L"));
    private static Formula LocalProjector(Formula s) => At(Q("D5", "S3", "Quantum", "Entanglement", "AbsoluteSeparability", "SymmetricAbsolutePPTPermutationFloor", "Local", "localP"), s);
    private static Formula Smul(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Cdot, Sp, Parenthesized(b));

    private static Formula Perms => At(Q("Equiv", "Perm"), X("I"));
    private static Formula Finsets => At(Q("Finset"), X("I"));
    private static Formula PermMatrix(Formula g) => Local("SymmetricAbsolutePPTPermutationFloor", "Q", g);
    private static Formula Card(Formula type) => At(Q("Fintype", "card"), type);
    private static Formula Stabilizer(Formula s) => At(Q("MulAction", "stabilizer"), Perms, s);
    private static Formula Fixed(Formula g) => At(Q("Subtype", "val"), g);
    private static Formula SymmetricDefinition() => FiniteTypes(All("v", Arr(Word, Complexes),
        Ifff(Sym(X("v")), All("sigma", Perms, All("x", Word,
            Eqn(At(X("v"), At(Q("Function", "comp"), X("x"), X("sigma"))), At(X("v"), X("x"))))))));
    private static Formula PermutationDefinition() => PermutationTypes(All("sigma", Perms,
        Eqn(PermMatrix(X("sigma")), At(Q("Equiv", "Perm", "permMatrix"), Complexes,
            At(Q("Equiv", "arrowCongr"), At(Q("Equiv", "symm"), X("sigma")), At(Q("Equiv", "refl"), X("L")))))));
    private static Formula ProjectorDefinition() => FiniteTypes(Eqn(Projector,
        At(Q("Finset", "expect"), Q("Finset", "univ"),
            Seq(Q("fun"), Sp, Typed(X("sigma"), Perms), Sp, Mapsto, Sp, PermMatrix(X("sigma"))))));
    private static Formula LocalDefinition() => LocalTypes(All("S", Finsets,
        Eqn(LocalProjector(X("S")), At(Q("Finset", "expect"), Q("Finset", "univ"),
            Seq(Q("fun"), Sp, Typed(X("g"), Stabilizer(X("S"))), Sp, Mapsto, Sp, PermMatrix(Fixed(X("g"))))))));
    private static Formula SymmetricRange() => FiniteTypes(All("v", Arr(Word, Complexes), Sym(MulVec(Projector, X("v")))));
    private static Formula FixedVectors() => FiniteTypes(All("v", Arr(Word, Complexes),
        Imp(Sym(X("v")), Eqn(MulVec(Projector, X("v")), X("v")))));
    private static Formula ProjectorHermitian() => FiniteTypes(Herm(Projector));
    private static Formula ProjectorIdempotent() => FiniteTypes(Eqn(Timesf(Projector, Projector), Projector));
    private static Formula LocalHermitian() => FiniteTypes(All("S", Finsets, Herm(LocalProjector(X("S")))));
    private static Formula LocalIdempotent() => FiniteTypes(All("S", Finsets,
        Eqn(Timesf(LocalProjector(X("S")), LocalProjector(X("S"))), LocalProjector(X("S")))));
    private static Formula LocalPositive() => FiniteTypes(All("S", Finsets, PSD(LocalProjector(X("S")))));
    private static Formula LocalFixesGlobal() => FiniteTypes(All("S", Finsets,
        Eqn(Timesf(LocalProjector(X("S")), Projector), Projector)));
    private static Formula TransposeSandwich() => FiniteTypes(All("S", Finsets, All("Y", Matrix(Word),
        Eqn(PT(X("S"), Timesf(Timesf(LocalProjector(X("S")), X("Y")), LocalProjector(X("S")))),
            Timesf(Timesf(LocalProjector(X("S")), PT(X("S"), X("Y"))), LocalProjector(X("S")))))));
    private static Formula TransposeFloor() => FiniteTypes(All("S", Finsets,
        PSD(Minusf(PT(X("S"), Projector), Smul(Inv(Typed(At(Q("Nat", "choose"),
            Card(X("I")), At(Q("Finset", "card"), X("S"))), Complexes)), LocalProjector(X("S")))))));

}
