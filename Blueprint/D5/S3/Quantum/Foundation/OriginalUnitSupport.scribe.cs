using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class OriginalUnitSupportDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/OriginalUnitSupport.";

    public DocumentDefinition Create()
    {
        Formula field = F.Id("F"), index = F.Id("iota"), space = F.Id("V"),
            cone = F.Id("C"), rho = F.Id("rho"), unit = F.Id("u"),
            x = F.Id("x"), y = F.Id("y"), z = F.Id("z");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula matrices = Call("Matrix", index, index, field);
        Formula vectors = Seq(index, To, Sp, field);
        Formula linear(Formula target) => Call("LinearMap", real, space, target);
        Formula app(Formula f, Formula a) => Seq(f, Open, a, Close);
        Formula mat(Formula a) => app(rho, a);
        Formula action(Formula a) => Call("mulVec", mat(a), z);
        Formula support = Call("commonSupport", cone, rho);
        Formula parameters(Formula body) => All("F", F.Id("Type"),
            All("iota", F.Id("Type"), All("V", F.Id("Type"), Seq(
                Bracket(Call("RCLike", field)), Sp,
                Bracket(Call("Fintype", index)), Sp,
                Bracket(Call("DecidableEq", index)), Sp,
                Bracket(Call("AddCommGroup", space)), Sp,
                Bracket(Call("Module", real, space)), Sp, body))));
        Formula objects(Formula body) => All("C", Call("PointedCone", real, space),
            All("rho", linear(matrices), body));
        Formula kernel = All("z", vectors, IffF(Eq(action(y), D(0)),
            All("x", space, Eq(action(x), D(0)))));
        Formula nativeVector = Call("ofLp", z);
        Formula positive = All("z", Call("EuclideanSpace", field, index),
            Imp(Member(z, support), Imp(Seq(z, Neq, Sp, D(0)),
                LtF(D(0), Call("re", Call("dotProduct", Call("star", nativeVector),
                    Call("mulVec", mat(y), nativeVector)))))));
        Formula conclusion = Ex("y", space, And(Member(y, cone),
            And(Eq(app(unit, y), D(1)), And(kernel,
                And(Eq(Call("range", Call("toEuclideanLin", mat(y))), support), positive)))));
        Formula statement = parameters(Seq(
            Bracket(Call("FiniteDimensional", real, space)), Sp,
            Bracket(Call("Nontrivial", space)), Sp,
            All("C", Call("PointedCone", real, space),
                Imp(Eq(Call("span", real, cone), Call("top", Call("Submodule", real, space))),
                    All("u", linear(real),
                        Imp(All("x", space, Imp(Member(x, cone),
                            Imp(Seq(x, Neq, Sp, D(0)), LtF(D(0), app(unit, x))))),
                            All("rho", linear(matrices),
                                Imp(Call("Injective", rho),
                                    Imp(All("x", space, Imp(Member(x, cone),
                                        Call("PosSemidef", mat(x)))), conclusion)))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "An arbitrary strictly positive original unit admits a state carrying the entire native PSD support.",
            H("Original unit and common matrix support"), Blocks(
                Paragraph(Text("Let F be a real or complex scalar field, represented by RCLike, and let iota be any finite decidable matrix index type. V is a nonzero finite dimensional real vector space. C is a pointed cone whose real linear span is V. The real linear map rho is injective and sends every member of C to a positive semidefinite native F-matrix. The original real linear unit u is strictly positive on every nonzero member of C. No trace normalization, positive definite ambient representative, rank-one generation, closedness, or compactness is needed for this support result.")),
                Describe.Lean(DescribeId.Create("common-support"),
                    DeclarationHandle.Create(Owner + "commonSupport"), H("Native common support"),
                    StatementSource.FromAuthor(Disp(parameters(objects(Eq(support,
                        Call("iSup", Seq(x, InMacro, Sp, cone, Mapsto, Sp,
                            Call("range", Call("toEuclideanLin", mat(x)))))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The supremum is in the lattice of F-linear subspaces of EuclideanSpace F iota and ranges over every original cone element. Thus a complex support has its complex dimension; it is not a realification. toEuclideanLin is the matrix action in the usual orthonormal coordinates."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("original-unit-full-support"),
                    DeclarationHandle.Create(Owner + "exists_original_unit_full_support"),
                    H("An original state with the entire common support"),
                    StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Finite dimensionality selects a finite spanning subset of the original cone. For its sum a, positive semidefiniteness makes a zero quadratic value force each summand to annihilate the same vector. Real spanning then propagates this annihilation to every represented original vector. Injectivity and nontriviality ensure a is nonzero. Hence u(a) is strictly positive and y = a / u(a) is an actual original state with exactly the same kernel. Hermitian orthogonal range-kernel duality identifies its range with the entire common support. A nonzero vector in that support has strictly positive quadratic value: otherwise it belongs to both the range and its orthogonal complement. This allows support-deficient ambient representations and includes support dimension one. ofLp denotes the ordinary coordinate vector of a Euclidean vector; re is the real part."))),
                    DescribeRole.Theorem),
                Paragraph(Text("The result supplies the original-unit positive-on-support candidate needed before determinant normalization. It does not construct support coordinates, the determinant maximizer, its uniqueness or stationarity, inverse-square-root congruence, a trace-preserving cone equivalence, or the returned order unit. Whole-base, pure-point, dual-effect, confirmation, exclusion, face and rank transport, together with fixed-complement and frame conclusions, require those further constructions. No classification or physical realization is inferred. The finite spanning, PSD quadratic-form and orthogonal-complement tools are standard; no literature priority is claimed.")))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula IffF(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Member(Formula left, Formula right) => Seq(left, InMacro, Sp, right);
    private static Formula LtF(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Bracket(Formula body) => Seq(OpenBracket, body, CloseBracket);
}
